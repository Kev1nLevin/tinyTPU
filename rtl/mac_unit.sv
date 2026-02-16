// =============================================================================
// Module: mac_unit
// Description: Multiply-Accumulate Unit (MAC)
//              Performs: acc = acc + (a * b)
//              Supports 8-bit signed inputs, 32-bit accumulator
//              Designed for ASAP7 7nm PDK
// =============================================================================

module mac_unit #(
    parameter DATA_WIDTH   = 8,    // Input operand width (INT8)
    parameter ACC_WIDTH    = 32    // Accumulator width
)(
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic                        en,           // Enable MAC operation
    input  logic                        clear_acc,    // Clear accumulator
    input  logic signed [DATA_WIDTH-1:0] a_in,        // Weight input
    input  logic signed [DATA_WIDTH-1:0] b_in,        // Activation input
    output logic signed [ACC_WIDTH-1:0]  acc_out      // Accumulated result
);

    // -------------------------------------------------------------------------
    // Internal signals
    // -------------------------------------------------------------------------
    logic signed [2*DATA_WIDTH-1:0] product;
    logic signed [ACC_WIDTH-1:0]    acc_reg;
    logic signed [ACC_WIDTH-1:0]    acc_next;

    // -------------------------------------------------------------------------
    // Multiply: signed 8b x 8b = 16b
    // -------------------------------------------------------------------------
    assign product = a_in * b_in;

    // -------------------------------------------------------------------------
    // Accumulate with saturation-safe addition (sign-extend product to 32b)
    // -------------------------------------------------------------------------
    assign acc_next = acc_reg + ACC_WIDTH'(product);

    // -------------------------------------------------------------------------
    // Sequential accumulator register
    // -------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            acc_reg <= '0;
        end else if (clear_acc) begin
            acc_reg <= '0;
        end else if (en) begin
            acc_reg <= acc_next;
        end
    end

    assign acc_out = acc_reg;

endmodule
