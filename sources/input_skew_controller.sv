// =============================================================================
// Module: input_skew_controller
// Description: Skews input data for systolic array feeding.
//              For correct matrix multiplication, inputs must be staggered:
//              - Row 0: feeds at cycle 0
//              - Row 1: feeds at cycle 1 (1 cycle delay)
//              - Row 2: feeds at cycle 2 (2 cycle delay)
//              - Row 3: feeds at cycle 3 (3 cycle delay)
//              This applies to both weight columns and activation rows.
//
//              The controller accepts a full 4-element vector and produces
//              a skewed version using shift registers.
// =============================================================================

module input_skew_controller #(
    parameter ARRAY_SIZE = 4,
    parameter DATA_WIDTH = 8
)(
    input  logic                         clk,
    input  logic                         rst_n,
    input  logic                         load_en,    // Enable data loading
    input  logic                         flush,      // Reset all skew registers

    // Input: flat 4-element vector (loaded every cycle during feeding)
    input  logic signed [DATA_WIDTH-1:0] data_in [ARRAY_SIZE],

    // Output: skewed version of input
    output logic signed [DATA_WIDTH-1:0] data_out [ARRAY_SIZE]
);

    // -------------------------------------------------------------------------
    // Skew shift registers
    // Channel 0: 0 delay stages (direct passthrough)
    // Channel 1: 1 delay stage
    // Channel 2: 2 delay stages
    // Channel 3: 3 delay stages
    // -------------------------------------------------------------------------

    // Channel 0 - no delay
    assign data_out[0] = load_en ? data_in[0] : '0;

    // Channel 1 - 1 stage delay
    logic signed [DATA_WIDTH-1:0] skew_1_r0;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            skew_1_r0 <= '0;
        else if (flush)
            skew_1_r0 <= '0;
        else if (load_en)
            skew_1_r0 <= data_in[1];
        else
            skew_1_r0 <= '0;
    end
    assign data_out[1] = skew_1_r0;

    // Channel 2 - 2 stage delay
    logic signed [DATA_WIDTH-1:0] skew_2_r0, skew_2_r1;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            skew_2_r0 <= '0;
            skew_2_r1 <= '0;
        end else if (flush) begin
            skew_2_r0 <= '0;
            skew_2_r1 <= '0;
        end else begin
            skew_2_r0 <= load_en ? data_in[2] : '0;
            skew_2_r1 <= skew_2_r0;
        end
    end
    assign data_out[2] = skew_2_r1;

    // Channel 3 - 3 stage delay
    logic signed [DATA_WIDTH-1:0] skew_3_r0, skew_3_r1, skew_3_r2;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            skew_3_r0 <= '0;
            skew_3_r1 <= '0;
            skew_3_r2 <= '0;
        end else if (flush) begin
            skew_3_r0 <= '0;
            skew_3_r1 <= '0;
            skew_3_r2 <= '0;
        end else begin
            skew_3_r0 <= load_en ? data_in[3] : '0;
            skew_3_r1 <= skew_3_r0;
            skew_3_r2 <= skew_3_r1;
        end
    end
    assign data_out[3] = skew_3_r2;

endmodule
