// =============================================================================
// Module: systolic_array_4x4
// Description: 4x4 Output-Stationary Systolic Array for Matrix Multiplication
//              Computes C = A x B where A, B are 4x4 matrices
//
//              Dataflow:
//              - Weights (A matrix) flow top-to-bottom (columns)
//              - Activations (B matrix) flow left-to-right (rows)
//              - Each PE accumulates partial products (output-stationary)
//
//              Architecture:
//                        a_col[0] a_col[1] a_col[2] a_col[3]
//                          |        |        |        |
//              b_row[0] --[PE00]--[PE01]--[PE02]--[PE03]-->
//              b_row[1] --[PE10]--[PE11]--[PE12]--[PE13]-->
//              b_row[2] --[PE20]--[PE21]--[PE22]--[PE23]-->
//              b_row[3] --[PE30]--[PE31]--[PE32]--[PE33]-->
//                          |        |        |        |
//
// =============================================================================

module systolic_array_4x4 #(
    parameter ARRAY_SIZE = 4,
    parameter DATA_WIDTH = 8,
    parameter ACC_WIDTH  = 32
)(
    input  logic                         clk,
    input  logic                         rst_n,
    input  logic                         en,
    input  logic                         clear_acc,

    // Weight inputs (top edge) - one per column
    input  logic signed [DATA_WIDTH-1:0] a_col [ARRAY_SIZE],

    // Activation inputs (left edge) - one per row
    input  logic signed [DATA_WIDTH-1:0] b_row [ARRAY_SIZE],

    // Result outputs - full 4x4 result matrix
    output logic signed [ACC_WIDTH-1:0]  result [ARRAY_SIZE][ARRAY_SIZE]
);

    // -------------------------------------------------------------------------
    // Internal wires for systolic interconnections
    // -------------------------------------------------------------------------
    // Horizontal wires (activation flow): b_wire[row][col]
    // b_wire[row][0] = input, b_wire[row][1..N] = PE outputs
    logic signed [DATA_WIDTH-1:0] b_wire [ARRAY_SIZE][ARRAY_SIZE+1];

    // Vertical wires (weight flow): a_wire[row][col]
    // a_wire[0][col] = input, a_wire[1..N][col] = PE outputs
    logic signed [DATA_WIDTH-1:0] a_wire [ARRAY_SIZE+1][ARRAY_SIZE];

    // -------------------------------------------------------------------------
    // Connect array inputs to wire mesh
    // -------------------------------------------------------------------------
    genvar i, j;

    generate
        // Connect top-edge weights
        for (i = 0; i < ARRAY_SIZE; i++) begin : gen_a_input
            assign a_wire[0][i] = a_col[i];
        end

        // Connect left-edge activations
        for (i = 0; i < ARRAY_SIZE; i++) begin : gen_b_input
            assign b_wire[i][0] = b_row[i];
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Generate 4x4 PE array with systolic interconnections
    // -------------------------------------------------------------------------
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

                    // From north / from west
                    .a_in       (a_wire[i][j]),
                    .b_in       (b_wire[i][j]),

                    // To south / to east
                    .a_out      (a_wire[i+1][j]),
                    .b_out      (b_wire[i][j+1]),

                    // Result
                    .result_out (result[i][j])
                );

            end // gen_col
        end // gen_row
    endgenerate

endmodule
