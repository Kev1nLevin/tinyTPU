// =============================================================================
// Module: input_skew_controller
// Description: Skews input data for systolic array feeding.
//              For correct matrix multiplication, inputs must be staggered:
//              - Channel 0: 0 delay (direct passthrough)
//              - Channel 1: 1 cycle delay
//              - Channel k: k cycle delay
//              - Channel N-1: N-1 cycle delay
//
//              Fully parameterized — works for any ARRAY_SIZE (4, 8, 16, etc.)
// =============================================================================

module input_skew_controller #(
    parameter ARRAY_SIZE = 4,
    parameter DATA_WIDTH = 8
)(
    input  logic                         clk,
    input  logic                         rst_n,
    input  logic                         load_en,    // Enable data loading
    input  logic                         flush,      // Reset all skew registers

    // Input: N-element vector (loaded every cycle during feeding)
    input  logic signed [DATA_WIDTH-1:0] data_in [ARRAY_SIZE],

    // Output: skewed version of input
    output logic signed [DATA_WIDTH-1:0] data_out [ARRAY_SIZE]
);

    // -------------------------------------------------------------------------
    // Generate skew shift registers for each channel
    // Channel k gets k delay stages
    // -------------------------------------------------------------------------
    genvar k;
    generate
        for (k = 0; k < ARRAY_SIZE; k++) begin : gen_skew_channel

            if (k == 0) begin : no_delay
                // Channel 0: no delay (direct passthrough when load_en)
                assign data_out[0] = load_en ? data_in[0] : '0;

            end else begin : with_delay
                // Channel k: k-stage shift register
                logic signed [DATA_WIDTH-1:0] sr [k];

                always_ff @(posedge clk or negedge rst_n) begin
                    if (!rst_n) begin
                        for (int i = 0; i < k; i++)
                            sr[i] <= '0;
                    end else if (flush) begin
                        for (int i = 0; i < k; i++)
                            sr[i] <= '0;
                    end else begin
                        // First stage takes input (or zero when not loading)
                        sr[0] <= load_en ? data_in[k] : '0;
                        // Subsequent stages shift
                        for (int i = 1; i < k; i++)
                            sr[i] <= sr[i-1];
                    end
                end

                // Output from last stage of shift register
                assign data_out[k] = sr[k-1];

            end
        end
    endgenerate

endmodule
