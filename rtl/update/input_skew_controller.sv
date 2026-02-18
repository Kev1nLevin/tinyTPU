// =============================================================================
// Module: input_skew_controller
// Description: Staggers an N-element input vector for systolic array feeding.
//              Channel k is delayed by k cycles (k = 0..N-1).
//              This creates the diagonal wavefront required for correct
//              matrix multiplication in an output-stationary systolic array.
// =============================================================================

module input_skew_controller #(
    parameter ARRAY_SIZE = 32,
    parameter DATA_WIDTH = 16
)(
    input  logic                         clk,
    input  logic                         rst_n,
    input  logic                         load_en,
    input  logic                         flush,

    input  logic signed [DATA_WIDTH-1:0] data_in [ARRAY_SIZE],
    output logic signed [DATA_WIDTH-1:0] data_out [ARRAY_SIZE]
);

    genvar k;
    generate
        for (k = 0; k < ARRAY_SIZE; k++) begin : gen_skew_channel

            if (k == 0) begin : no_delay
                // Channel 0: zero delay — pass through or zero
                assign data_out[0] = load_en ? data_in[0] : '0;

            end else begin : with_delay
                // Channel k: k-stage shift register
                logic signed [DATA_WIDTH-1:0] sr [k];

                always_ff @(posedge clk or negedge rst_n) begin
                    if (!rst_n) begin
                        for (int i = 0; i < k; i++) sr[i] <= '0;
                    end else if (flush) begin
                        for (int i = 0; i < k; i++) sr[i] <= '0;
                    end else begin
                        sr[0] <= load_en ? data_in[k] : '0;
                        for (int i = 1; i < k; i++)
                            sr[i] <= sr[i-1];
                    end
                end

                assign data_out[k] = sr[k-1];
            end
        end
    endgenerate

endmodule
