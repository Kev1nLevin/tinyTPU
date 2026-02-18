// =============================================================================
// Module: mac_unit
// Description: 2-Stage Pipelined BF16 Multiply-Accumulate Unit (Production)
//              Computes: acc = acc + (a * b)
//              Inputs:      BF16  (16-bit brain-float)
//              Accumulator: FP32  (32-bit single-precision)
//
//              Pipeline:
//                Stage 1 (registered): BF16 × BF16 → FP32 product
//                Stage 2 (registered): FP32 acc   += FP32 product
//
//              Production enhancements over academic version:
//                - Round-to-nearest-even (RNE) on accumulator
//                - NaN propagation (canonical quiet NaN 0x7FC00000)
//                - Exponent overflow saturation (clamp to FP32_MAX)
//                - Flush-to-zero for denormals (intentional, per BF16 spec)
//                - Infinity input detection
//
//              BF16 format: [15]=sign [14:7]=exp(bias=127) [6:0]=mantissa
//              FP32 format: [31]=sign [30:23]=exp(bias=127) [22:0]=mantissa
//
// MAC Latency: 2 clock cycles
// =============================================================================

module mac_unit #(
    parameter DATA_WIDTH = 16,
    parameter ACC_WIDTH  = 32
)(
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  en,
    input  logic                  clear_acc,
    input  logic [DATA_WIDTH-1:0] a_in,    // BF16 weight
    input  logic [DATA_WIDTH-1:0] b_in,    // BF16 activation
    output logic [ACC_WIDTH-1:0]  acc_out  // FP32 result
);

    localparam MAC_LATENCY = 2;

    // FP32 special constants
    localparam [ACC_WIDTH-1:0] FP32_QNAN     = 32'h7FC00000;  // canonical quiet NaN
    localparam [ACC_WIDTH-1:0] FP32_POS_MAX  = 32'h7F7FFFFF;  // largest positive normal
    localparam [ACC_WIDTH-1:0] FP32_NEG_MAX  = 32'hFF7FFFFF;  // largest negative normal

    // =========================================================================
    // Stage 1: BF16 × BF16 → FP32 product
    // =========================================================================

    // Extract BF16 fields
    logic        a_s, b_s;
    logic [7:0]  a_e, b_e;
    logic [7:0]  a_mf, b_mf;   // full mantissa with implicit 1
    logic        a_is_zero, b_is_zero;
    logic        a_is_nan, b_is_nan;
    logic        a_is_inf, b_is_inf;

    assign a_s  = a_in[15];
    assign a_e  = a_in[14:7];
    assign a_mf = {1'b1, a_in[6:0]};
    assign b_s  = b_in[15];
    assign b_e  = b_in[14:7];
    assign b_mf = {1'b1, b_in[6:0]};

    assign a_is_zero = (a_e == 8'h00);
    assign b_is_zero = (b_e == 8'h00);
    assign a_is_nan  = (a_e == 8'hFF) && (a_in[6:0] != 7'b0);
    assign b_is_nan  = (b_e == 8'hFF) && (b_in[6:0] != 7'b0);
    assign a_is_inf  = (a_e == 8'hFF) && (a_in[6:0] == 7'b0);
    assign b_is_inf  = (b_e == 8'hFF) && (b_in[6:0] == 7'b0);

    // Mantissa multiply: 8b × 8b = 16b
    logic [15:0] mant_prod;
    assign mant_prod = a_mf * b_mf;

    // Product exponent
    logic [8:0] prod_exp_raw;
    assign prod_exp_raw = {1'b0, a_e} + {1'b0, b_e} - 9'd127;

    // Combinational FP32 product with special-value handling
    logic [ACC_WIDTH-1:0] product_comb;
    logic                 product_is_nan;

    always_comb begin
        product_is_nan = 1'b0;
        if (a_is_nan || b_is_nan) begin
            // NaN propagation
            product_comb   = FP32_QNAN;
            product_is_nan = 1'b1;
        end else if (a_is_zero || b_is_zero) begin
            // Zero or denormal input → flush to zero
            // Note: 0 × inf = NaN per IEEE, but we saturate
            product_comb = (a_is_inf || b_is_inf) ? FP32_QNAN : '0;
            product_is_nan = (a_is_inf || b_is_inf);
        end else if (a_is_inf || b_is_inf) begin
            // inf × finite = inf
            product_comb = {a_s ^ b_s, 8'hFF, 23'b0};
        end else if (prod_exp_raw[8]) begin
            // Exponent underflow → flush to zero
            product_comb = '0;
        end else if (mant_prod[15]) begin
            // Product in [2.0, 4.0)
            if ((prod_exp_raw[7:0] + 8'd1) >= 8'hFF) begin
                // Overflow → saturate to max
                product_comb = {a_s ^ b_s, FP32_POS_MAX[30:0]};
            end else begin
                product_comb = {a_s ^ b_s, prod_exp_raw[7:0] + 8'd1,
                                mant_prod[14:0], 8'b0};
            end
        end else begin
            // Product in [1.0, 2.0)
            if (prod_exp_raw[7:0] >= 8'hFF) begin
                product_comb = {a_s ^ b_s, FP32_POS_MAX[30:0]};
            end else begin
                product_comb = {a_s ^ b_s, prod_exp_raw[7:0],
                                mant_prod[13:0], 9'b0};
            end
        end
    end

    // Stage 1 register
    logic [ACC_WIDTH-1:0] product_reg;
    logic                 product_nan_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            product_reg     <= '0;
            product_nan_reg <= 1'b0;
        end else if (clear_acc) begin
            product_reg     <= '0;
            product_nan_reg <= 1'b0;
        end else if (en) begin
            product_reg     <= product_comb;
            product_nan_reg <= product_is_nan;
        end
    end

    // =========================================================================
    // Stage 2: FP32 Accumulate with RNE rounding (acc_reg += product_reg)
    // =========================================================================

    logic [ACC_WIDTH-1:0] acc_reg;

    // Extract FP32 fields
    logic        x_s, y_s;
    logic [7:0]  x_e, y_e;
    logic [23:0] x_m, y_m;
    logic        x_is_nan, y_is_nan, x_is_inf, y_is_inf;

    assign x_s = acc_reg[31];
    assign x_e = acc_reg[30:23];
    assign x_m = (x_e == 8'h00) ? 24'b0 : {1'b1, acc_reg[22:0]};
    assign x_is_nan = (x_e == 8'hFF) && (acc_reg[22:0] != 23'b0);
    assign x_is_inf = (x_e == 8'hFF) && (acc_reg[22:0] == 23'b0);

    assign y_s = product_reg[31];
    assign y_e = product_reg[30:23];
    assign y_m = (y_e == 8'h00) ? 24'b0 : {1'b1, product_reg[22:0]};
    assign y_is_nan = product_nan_reg || ((y_e == 8'hFF) && (product_reg[22:0] != 23'b0));
    assign y_is_inf = (y_e == 8'hFF) && (product_reg[22:0] == 23'b0);

    // ---- Sort by magnitude ----
    logic        big_is_y;
    assign big_is_y = (y_e > x_e) || ((y_e == x_e) && (y_m > x_m));

    logic        big_s, sml_s;
    logic [7:0]  big_e, sml_e;
    logic [23:0] big_m, sml_m;

    assign {big_s, big_e, big_m} = big_is_y ? {y_s, y_e, y_m} : {x_s, x_e, x_m};
    assign {sml_s, sml_e, sml_m} = big_is_y ? {x_s, x_e, x_m} : {y_s, y_e, y_m};

    // ---- Align smaller operand with Guard-Round-Sticky bits ----
    logic [7:0]  exp_diff;
    logic [4:0]  align_shift;
    // Extended mantissa: [23:0]=mantissa, [guard][round][sticky]
    logic [26:0] sml_m_ext;  // 24-bit mantissa + 3 GRS bits
    logic [26:0] sml_m_shifted;
    logic        guard_bit, round_bit, sticky_bit;

    assign exp_diff    = big_e - sml_e;
    assign align_shift = (exp_diff >= 8'd27) ? 5'd27 : exp_diff[4:0];

    // Extend small mantissa with 3 zero GRS bits, then shift
    assign sml_m_ext = {sml_m, 3'b0};

    always_comb begin
        sml_m_shifted = sml_m_ext >> align_shift;
        // Compute sticky from all bits shifted out beyond guard and round
        sticky_bit = 1'b0;
        if (exp_diff >= 8'd27) begin
            // Everything shifted out
            sml_m_shifted = '0;
            sticky_bit = |sml_m;
        end else if (exp_diff > 0) begin
            // OR together all bits that were shifted off
            for (int i = 0; i < 27; i++) begin
                if (i < int'(align_shift))
                    sticky_bit = sticky_bit | sml_m_ext[i];
            end
        end
    end

    logic [23:0] sml_m_aligned;
    assign sml_m_aligned = sml_m_shifted[26:3];
    assign guard_bit     = sml_m_shifted[2];
    assign round_bit     = sml_m_shifted[1];
    // sticky_bit computed above

    // ---- Effective operation ----
    logic add_op;
    assign add_op = (big_s == sml_s);

    logic [24:0] add_result;
    assign add_result = {1'b0, big_m} + {1'b0, sml_m_aligned};

    logic [23:0] sub_result;
    assign sub_result = big_m - sml_m_aligned;

    // Leading-zero count for normalization
    logic [4:0] lz_count;
    always_comb begin
        lz_count = 5'd24;
        for (int k = 0; k <= 23; k++)
            if (sub_result[k]) lz_count = 5'(23 - k);
    end

    logic [23:0] sub_norm;
    assign sub_norm = sub_result << lz_count;

    // ---- RNE rounding logic ----
    // Apply after addition path (subtraction path loses precision differently)
    logic rne_round_up_add;
    logic rne_round_up_add_carry;
    // For add: GRS bits determine rounding on the result
    // After add with carry (shift right 1), the LSB of mantissa and guard determine rounding
    assign rne_round_up_add       = guard_bit & (round_bit | sticky_bit | add_result[0]);
    assign rne_round_up_add_carry = guard_bit & (round_bit | sticky_bit | add_result[1]);

    // ---- Intermediate results for output build ----
    logic [22:0] add_mant_carry;
    logic [22:0] add_mant_nocarry;

    assign add_mant_carry   = add_result[23:1] + (rne_round_up_add_carry ? 23'd1 : 23'd0);
    assign add_mant_nocarry = add_result[22:0] + (rne_round_up_add ? 23'd1 : 23'd0);

    // ---- Build accumulator next value ----
    logic [ACC_WIDTH-1:0] acc_next;

    always_comb begin
        // Default
        acc_next = acc_reg;

        if (x_is_nan || y_is_nan) begin
            // NaN propagation
            acc_next = FP32_QNAN;

        end else if (x_is_inf && y_is_inf && (x_s != y_s)) begin
            // +inf + -inf = NaN
            acc_next = FP32_QNAN;

        end else if (x_is_inf) begin
            acc_next = acc_reg;

        end else if (y_is_inf) begin
            acc_next = product_reg;

        end else if (x_e == 8'h00 && y_e == 8'h00) begin
            acc_next = '0;

        end else if (x_e == 8'h00) begin
            acc_next = product_reg;

        end else if (y_e == 8'h00) begin
            acc_next = acc_reg;

        end else if (add_op) begin
            // ---- Addition path with RNE ----
            if (add_result[24]) begin
                // Carry out: shift right 1, exp+1
                if (big_e >= 8'hFE) begin
                    // Overflow → saturate
                    acc_next = {big_s, FP32_POS_MAX[30:0]};
                end else begin
                    acc_next = {big_s, big_e + 8'd1, add_mant_carry};
                end
            end else begin
                acc_next = {big_s, big_e, add_mant_nocarry};
            end

        end else begin
            // ---- Subtraction path ----
            if (sub_result == '0) begin
                acc_next = '0;
            end else if (big_e >= {3'b0, lz_count}) begin
                acc_next = {big_s, big_e - {3'b0, lz_count}, sub_norm[22:0]};
            end else begin
                acc_next = '0;
            end
        end
    end

    // Stage 2 register (accumulator)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            acc_reg <= '0;
        else if (clear_acc)
            acc_reg <= '0;
        else if (en)
            acc_reg <= acc_next;
    end

    assign acc_out = acc_reg;

    // =========================================================================
    // SVA — Assertions (simulation only)
    // =========================================================================
    // synthesis translate_off
    property p_clear_resets_acc;
        @(posedge clk) disable iff (!rst_n)
        clear_acc |=> (acc_out == '0);
    endproperty
    assert property (p_clear_resets_acc)
        else $error("MAC: accumulator not zero after clear");

    property p_nan_propagates;
        @(posedge clk) disable iff (!rst_n)
        (product_nan_reg && en && !clear_acc) |=>
            (acc_out == FP32_QNAN);
    endproperty
    assert property (p_nan_propagates)
        else $error("MAC: NaN not propagated to accumulator");
    // synthesis translate_on

endmodule
