// =============================================================================
// Module: systolic_top
// Description: Top-level systolic array datapath (Production)
//              Orchestrates: input SRAMs → skew controllers → PE array →
//              result drain → activation → result SRAM.
//
//              Production enhancements:
//              - SRAM-based input storage (mat_a, mat_b) with double buffering
//              - SRAM-based result storage (drained from PE array)
//              - Registered activation unit (multi-function: NONE/ReLU/GeLU)
//              - Bias addition (per-column FP32 bias register file)
//              - Performance counters
//              - Accumulate mode for tiling
//              - Cleaned signal naming (col/row instead of a/b confusion)
//
//              Memory Map (per bank):
//              SRAM A: 32 rows × 512 bits  (32 BF16 values/row = weights)
//              SRAM B: 32 rows × 512 bits  (32 BF16 values/row = activations)
//              SRAM R: 32 rows × 1024 bits (32 FP32 values/row = results)
//
//              Latency: 1(CLEAR) + 32(LOAD) + 63(DRAIN) + 32(DRAIN_RESULT) + 1(DONE) = 129 cycles
// =============================================================================

module systolic_top #(
    parameter ARRAY_SIZE  = 32,
    parameter DATA_WIDTH  = 16,    // BF16
    parameter ACC_WIDTH   = 32,    // FP32
    parameter MAC_LATENCY = 2,
    parameter ENABLE_DOUBLE_BUF = 1  // 1 = double buffering, 0 = single buffer
)(
    input  logic        clk,
    input  logic        rst_n,

    // Control interface (from AXI wrapper)
    input  logic        tpu_start,
    input  logic        acc_mode,      // 1 = skip clear, accumulate on existing
    output logic        tpu_busy,
    output logic        tpu_done,

    // Activation config
    input  logic [2:0]  act_func,      // 3'b000=NONE, 3'b001=ReLU, 3'b010=GeLU

    // ---- Write port: CPU → input SRAMs (matrix loading) ----
    input  logic        wr_en_a,
    input  logic        wr_en_b,
    input  logic [$clog2(ARRAY_SIZE)-1:0] wr_row_addr,
    input  logic signed [DATA_WIDTH-1:0]  wr_data [ARRAY_SIZE],

    // ---- Read port: CPU ← result SRAM ----
    input  logic [$clog2(ARRAY_SIZE)-1:0] rd_row_addr,
    input  logic        rd_en,
    output logic signed [ACC_WIDTH-1:0]   rd_data [ARRAY_SIZE],
    output logic        rd_valid,

    // ---- Bias register file write port ----
    input  logic        bias_wr_en,
    input  logic [$clog2(ARRAY_SIZE)-1:0] bias_wr_addr,
    input  logic [ACC_WIDTH-1:0]          bias_wr_data,
    input  logic        bias_en,

    // Performance counters (read-only)
    output logic [31:0] perf_total_cycles,
    output logic [31:0] perf_compute_cycles,
    output logic [31:0] perf_idle_cycles
);

    localparam ADDR_W = $clog2(ARRAY_SIZE);
    localparam ROW_BITS_IN  = ARRAY_SIZE * DATA_WIDTH;   // 32×16 = 512
    localparam ROW_BITS_OUT = ARRAY_SIZE * ACC_WIDTH;    // 32×32 = 1024
    localparam CNT_W = $clog2(3*ARRAY_SIZE + MAC_LATENCY);

    // =========================================================================
    // Controller
    // =========================================================================
    logic        pe_en, pe_clear_acc, skew_load_en, skew_flush;
    logic        drain_result_en;
    logic [CNT_W-1:0] drain_row;
    logic [CNT_W-1:0] cycle_count;

    systolic_controller #(
        .ARRAY_SIZE  (ARRAY_SIZE),
        .MAC_LATENCY (MAC_LATENCY)
    ) u_ctrl (
        .clk             (clk),
        .rst_n           (rst_n),
        .start           (tpu_start),
        .acc_mode        (acc_mode),
        .busy            (tpu_busy),
        .done            (tpu_done),
        .pe_en           (pe_en),
        .pe_clear_acc    (pe_clear_acc),
        .skew_load_en    (skew_load_en),
        .skew_flush      (skew_flush),
        .drain_result_en (drain_result_en),
        .drain_row       (drain_row),
        .cycle_count     (cycle_count)
    );

    // =========================================================================
    // Double-buffer bank selection
    // =========================================================================
    logic bank_sel;  // toggles on each start

    generate
        if (ENABLE_DOUBLE_BUF) begin : gen_double_buf
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    bank_sel <= 1'b0;
                else if (tpu_start)
                    bank_sel <= ~bank_sel;
            end
        end else begin : gen_single_buf
            assign bank_sel = 1'b0;
        end
    endgenerate

    // CPU writes go to the SHADOW bank (opposite of active compute bank)
    logic cpu_bank, compute_bank;
    assign compute_bank = bank_sel;
    assign cpu_bank     = ENABLE_DOUBLE_BUF ? ~bank_sel : 1'b0;

    // =========================================================================
    // Input SRAMs (mat_a, mat_b) — 2 banks if double buffered
    // =========================================================================
    // SRAM A
    logic [ROW_BITS_IN-1:0] sram_a_dout [ENABLE_DOUBLE_BUF ? 2 : 1];
    logic [ROW_BITS_IN-1:0] sram_a_din;
    logic [ADDR_W-1:0]      sram_a_addr [ENABLE_DOUBLE_BUF ? 2 : 1];
    logic                   sram_a_we [ENABLE_DOUBLE_BUF ? 2 : 1];
    logic                   sram_a_ce [ENABLE_DOUBLE_BUF ? 2 : 1];

    // SRAM B
    logic [ROW_BITS_IN-1:0] sram_b_dout [ENABLE_DOUBLE_BUF ? 2 : 1];
    logic [ROW_BITS_IN-1:0] sram_b_din;
    logic [ADDR_W-1:0]      sram_b_addr [ENABLE_DOUBLE_BUF ? 2 : 1];
    logic                   sram_b_we [ENABLE_DOUBLE_BUF ? 2 : 1];
    logic                   sram_b_ce [ENABLE_DOUBLE_BUF ? 2 : 1];

    // Pack write data into flat vector
    genvar gi;
    generate
        for (gi = 0; gi < ARRAY_SIZE; gi++) begin : gen_pack_wr
            assign sram_a_din[gi*DATA_WIDTH +: DATA_WIDTH] = wr_data[gi];
            assign sram_b_din[gi*DATA_WIDTH +: DATA_WIDTH] = wr_data[gi];
        end
    endgenerate

    // Address/control mux for each bank
    generate
        for (gi = 0; gi < (ENABLE_DOUBLE_BUF ? 2 : 1); gi++) begin : gen_sram_ab
            localparam int BANK = gi;

            // SRAM A address mux
            always_comb begin
                if (BANK == compute_bank && tpu_busy) begin
                    // Controller reads during LOAD phase
                    sram_a_addr[BANK] = cycle_count[ADDR_W-1:0];
                    sram_a_we[BANK]   = 1'b0;
                    sram_a_ce[BANK]   = skew_load_en;
                end else if (BANK == cpu_bank) begin
                    // CPU writes when not busy (single buf) or to shadow bank (double buf)
                    sram_a_addr[BANK] = wr_row_addr;
                    sram_a_we[BANK]   = wr_en_a;
                    sram_a_ce[BANK]   = wr_en_a;
                end else begin
                    sram_a_addr[BANK] = '0;
                    sram_a_we[BANK]   = 1'b0;
                    sram_a_ce[BANK]   = 1'b0;
                end
            end

            // SRAM B address mux
            always_comb begin
                if (BANK == compute_bank && tpu_busy) begin
                    sram_b_addr[BANK] = cycle_count[ADDR_W-1:0];
                    sram_b_we[BANK]   = 1'b0;
                    sram_b_ce[BANK]   = skew_load_en;
                end else if (BANK == cpu_bank) begin
                    sram_b_addr[BANK] = wr_row_addr;
                    sram_b_we[BANK]   = wr_en_b;
                    sram_b_ce[BANK]   = wr_en_b;
                end else begin
                    sram_b_addr[BANK] = '0;
                    sram_b_we[BANK]   = 1'b0;
                    sram_b_ce[BANK]   = 1'b0;
                end
            end

            // Instantiate SRAM macros
            sram_sp #(
                .DEPTH     (ARRAY_SIZE),
                .WIDTH     (ROW_BITS_IN)
            ) u_sram_a (
                .clk  (clk),
                .ce   (sram_a_ce[BANK]),
                .we   (sram_a_we[BANK]),
                .addr (sram_a_addr[BANK]),
                .din  (sram_a_din),
                .dout (sram_a_dout[BANK])
            );

            sram_sp #(
                .DEPTH     (ARRAY_SIZE),
                .WIDTH     (ROW_BITS_IN)
            ) u_sram_b (
                .clk  (clk),
                .ce   (sram_b_ce[BANK]),
                .we   (sram_b_we[BANK]),
                .addr (sram_b_addr[BANK]),
                .din  (sram_b_din),
                .dout (sram_b_dout[BANK])
            );
        end
    endgenerate

    // Active SRAM read data (from compute bank)
    logic [ROW_BITS_IN-1:0] active_a_row, active_b_row;
    assign active_a_row = sram_a_dout[compute_bank];
    assign active_b_row = sram_b_dout[compute_bank];

    // =========================================================================
    // Unpack SRAM rows into per-element signals
    // =========================================================================
    logic signed [DATA_WIDTH-1:0] col_feed_raw [ARRAY_SIZE]; // columns (weight A)
    logic signed [DATA_WIDTH-1:0] row_feed_raw [ARRAY_SIZE]; // rows (activ B)

    generate
        for (gi = 0; gi < ARRAY_SIZE; gi++) begin : gen_unpack
            assign col_feed_raw[gi] = active_a_row[gi*DATA_WIDTH +: DATA_WIDTH];
            assign row_feed_raw[gi] = active_b_row[gi*DATA_WIDTH +: DATA_WIDTH];
        end
    endgenerate

    // =========================================================================
    // Skew Controllers
    // =========================================================================
    logic signed [DATA_WIDTH-1:0] col_skewed [ARRAY_SIZE];
    logic signed [DATA_WIDTH-1:0] row_skewed [ARRAY_SIZE];

    input_skew_controller #(
        .ARRAY_SIZE (ARRAY_SIZE),
        .DATA_WIDTH (DATA_WIDTH)
    ) u_skew_col (
        .clk      (clk),
        .rst_n    (rst_n),
        .load_en  (skew_load_en),
        .flush    (skew_flush),
        .data_in  (col_feed_raw),
        .data_out (col_skewed)
    );

    input_skew_controller #(
        .ARRAY_SIZE (ARRAY_SIZE),
        .DATA_WIDTH (DATA_WIDTH)
    ) u_skew_row (
        .clk      (clk),
        .rst_n    (rst_n),
        .load_en  (skew_load_en),
        .flush    (skew_flush),
        .data_in  (row_feed_raw),
        .data_out (row_skewed)
    );

    // =========================================================================
    // Systolic Array
    // =========================================================================
    logic signed [ACC_WIDTH-1:0] pe_result [ARRAY_SIZE][ARRAY_SIZE];

    systolic_array #(
        .ARRAY_SIZE (ARRAY_SIZE),
        .DATA_WIDTH (DATA_WIDTH),
        .ACC_WIDTH  (ACC_WIDTH)
    ) u_array (
        .clk       (clk),
        .rst_n     (rst_n),
        .en        (pe_en),
        .clear_acc (pe_clear_acc),
        .a_col     (col_skewed),
        .b_row     (row_skewed),
        .result    (pe_result)
    );

    // =========================================================================
    // Bias Register File (32 × FP32)
    // =========================================================================
    logic [ACC_WIDTH-1:0] bias_rf [ARRAY_SIZE];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < ARRAY_SIZE; i++)
                bias_rf[i] <= '0;
        end else if (bias_wr_en) begin
            bias_rf[bias_wr_addr] <= bias_wr_data;
        end
    end

    // =========================================================================
    // Result Drain Pipeline → Activation Units → Result SRAM
    // =========================================================================
    // During DRAIN_RESULT (N cycles), read one row from PE array per cycle,
    // pass through activation, write to result SRAM.

    // Current drain row data (from PE array)
    logic signed [ACC_WIDTH-1:0] drain_row_data [ARRAY_SIZE];
    logic [ADDR_W-1:0] drain_row_addr;

    assign drain_row_addr = drain_row[ADDR_W-1:0];

    // Mux: select one row from 2D PE result array
    always_comb begin
        for (int j = 0; j < ARRAY_SIZE; j++)
            drain_row_data[j] = pe_result[drain_row_addr][j];
    end

    // Apply bias (simple FP32 add — for production, use a proper FP adder;
    // here we pass pre-biased values through activation unit which handles it)
    // For simplicity, bias is added at drain time as an integer add approximation.
    // A full FP32 adder per column would be ideal but adds area.
    // We pass bias to activation_unit for future expansion.

    // Activation unit per column (registered output)
    logic [ACC_WIDTH-1:0] act_out [ARRAY_SIZE];
    logic                 act_valid [ARRAY_SIZE];

    generate
        for (gi = 0; gi < ARRAY_SIZE; gi++) begin : gen_act
            activation_unit u_act (
                .clk       (clk),
                .rst_n     (rst_n),
                .valid_in  (drain_result_en),
                .fp32_in   (drain_row_data[gi]),
                .act_func  (act_func),
                .bias_val  (bias_rf[gi]),
                .bias_en   (bias_en),
                .fp32_out  (act_out[gi]),
                .valid_out (act_valid[gi])
            );
        end
    endgenerate

    // =========================================================================
    // Result SRAM (written during DRAIN_RESULT, read by CPU anytime)
    // =========================================================================
    logic [ROW_BITS_OUT-1:0] result_sram_din;
    logic [ROW_BITS_OUT-1:0] result_sram_dout;
    logic [ADDR_W-1:0]       result_sram_addr;
    logic                    result_sram_we;
    logic                    result_sram_ce;

    // Pack activation outputs into flat vector for SRAM write
    generate
        for (gi = 0; gi < ARRAY_SIZE; gi++) begin : gen_pack_result
            assign result_sram_din[gi*ACC_WIDTH +: ACC_WIDTH] = act_out[gi];
        end
    endgenerate

    // Drain write address is delayed by 1 cycle (activation unit latency)
    logic [ADDR_W-1:0] drain_row_addr_d1;
    logic              drain_result_en_d1;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            drain_row_addr_d1  <= '0;
            drain_result_en_d1 <= 1'b0;
        end else begin
            drain_row_addr_d1  <= drain_row_addr;
            drain_result_en_d1 <= drain_result_en;
        end
    end

    // Result SRAM address/control mux
    always_comb begin
        if (drain_result_en_d1) begin
            // Write path: drain results from activation units
            result_sram_addr = drain_row_addr_d1;
            result_sram_we   = 1'b1;
            result_sram_ce   = 1'b1;
        end else begin
            // Read path: CPU reads results
            result_sram_addr = rd_row_addr;
            result_sram_we   = 1'b0;
            result_sram_ce   = rd_en;
        end
    end

    sram_sp #(
        .DEPTH     (ARRAY_SIZE),
        .WIDTH     (ROW_BITS_OUT)
    ) u_sram_result (
        .clk  (clk),
        .ce   (result_sram_ce),
        .we   (result_sram_we),
        .addr (result_sram_addr),
        .din  (result_sram_din),
        .dout (result_sram_dout)
    );

    // Unpack result SRAM output for CPU read
    logic rd_valid_d1;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rd_valid_d1 <= 1'b0;
        else
            rd_valid_d1 <= rd_en && !drain_result_en_d1;
    end
    assign rd_valid = rd_valid_d1;

    generate
        for (gi = 0; gi < ARRAY_SIZE; gi++) begin : gen_unpack_result
            assign rd_data[gi] = result_sram_dout[gi*ACC_WIDTH +: ACC_WIDTH];
        end
    endgenerate

    // =========================================================================
    // Performance Counters
    // =========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            perf_total_cycles   <= '0;
            perf_compute_cycles <= '0;
            perf_idle_cycles    <= '0;
        end else begin
            perf_total_cycles <= perf_total_cycles + 32'd1;
            if (tpu_busy)
                perf_compute_cycles <= perf_compute_cycles + 32'd1;
            else
                perf_idle_cycles <= perf_idle_cycles + 32'd1;
        end
    end

endmodule
