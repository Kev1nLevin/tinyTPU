// =============================================================================
// Module: systolic_array
// Description: NxN Output-Stationary Systolic Array for Matrix Multiplication
//              Computes C = A x B where A, B are NxN matrices.
//              N² PEs — parameterized size (validated power-of-2).
//
//              Dataflow:
//              - Weights (A matrix) flow top-to-bottom (columns via a_col)
//              - Activations (B matrix) flow left-to-right (rows via b_row)
//              - Each PE accumulates partial products (output-stationary)
// =============================================================================

module systolic_array #(
    parameter ARRAY_SIZE = 32,
    parameter DATA_WIDTH = 16,
    parameter ACC_WIDTH  = 32
)(
    input  logic                         clk,
    input  logic                         rst_n,
    input  logic                         en,
    input  logic                         clear_acc,

    // Weight inputs (top edge) — one per column
    input  logic signed [DATA_WIDTH-1:0] a_col [ARRAY_SIZE],

    // Activation inputs (left edge) — one per row
    input  logic signed [DATA_WIDTH-1:0] b_row [ARRAY_SIZE],

    // Result outputs — full NxN result matrix
    output logic signed [ACC_WIDTH-1:0]  result [ARRAY_SIZE][ARRAY_SIZE]
);

    // =========================================================================
    // Parameter validation
    // =========================================================================
    // synthesis translate_off
    initial begin
        assert (ARRAY_SIZE > 0 && (ARRAY_SIZE & (ARRAY_SIZE - 1)) == 0)
            else $fatal(1, "ARRAY_SIZE must be a power of 2, got %0d", ARRAY_SIZE);
        assert (DATA_WIDTH == 16)
            else $fatal(1, "Only BF16 (16-bit) inputs currently supported");
        assert (ACC_WIDTH == 32)
            else $fatal(1, "Only FP32 (32-bit) accumulators currently supported");
    end
    // synthesis translate_on

    // =========================================================================
    // Inter-PE wiring
    // =========================================================================
    // Horizontal: b_wire[row][0] = left-edge input, [1..N] = PE pass-through
    logic signed [DATA_WIDTH-1:0] b_wire [ARRAY_SIZE][ARRAY_SIZE+1];
    // Vertical:   a_wire[0][col] = top-edge input,  [1..N] = PE pass-through
    logic signed [DATA_WIDTH-1:0] a_wire [ARRAY_SIZE+1][ARRAY_SIZE];

    genvar i, j;

    // Connect edge inputs
    generate
        for (i = 0; i < ARRAY_SIZE; i++) begin : gen_a_input
            assign a_wire[0][i] = a_col[i];
        end
        for (i = 0; i < ARRAY_SIZE; i++) begin : gen_b_input
            assign b_wire[i][0] = b_row[i];
        end
    endgenerate

    // Instantiate PE grid
    generate
        for (i = 0; i < ARRAY_SIZE; i++) begin : gen_row
            for (j = 0; j < ARRAY_SIZE; j++) begin : gen_col

                processing_element #(
                    .DATA_WIDTH (DATA_WIDTH),
                    .ACC_WIDTH  (ACC_WIDTH)
                ) u_pe (
                    .clk        (clk),
                    .rst_n      (rst_n),
                    .en         (en),
                    .clear_acc  (clear_acc),
                    .a_in       (a_wire[i][j]),
                    .b_in       (b_wire[i][j]),
                    .a_out      (a_wire[i+1][j]),
                    .b_out      (b_wire[i][j+1]),
                    .result_out (result[i][j])
                );

            end
        end
    endgenerate

endmodule
