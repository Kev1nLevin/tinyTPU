// =============================================================================
// Module: systolic_top
// Description: Top-level Neural Network MAC Accelerator
//              Integrates:
//              - NxN Systolic Array (N² PEs)
//              - Input Skew Controllers (weight & activation)
//              - FSM Controller
//              - Input register files for A and B matrices
//
//              Dataflow for C = A × B:
//              - B columns flow top-to-bottom through a_col (vertical)
//              - A rows flow left-to-right through b_row (horizontal)
//              - PE[i][j] accumulates: sum_k A[i][k] * B[k][j]
//
//              Fully parameterized — works for any ARRAY_SIZE (4, 8, 16, etc.)
//              Target: ASAP7 7nm PDK
// =============================================================================

module systolic_top #(
    parameter ARRAY_SIZE = 4,
    parameter DATA_WIDTH = 8,
    parameter ACC_WIDTH  = 32,
    parameter ADDR_WIDTH = $clog2(ARRAY_SIZE),
    parameter CNT_WIDTH  = $clog2(3*ARRAY_SIZE)
)(
    input  logic                         clk,
    input  logic                         rst_n,

    // ---- Matrix Load Interface ----
    input  logic                         wr_en_a,     // Write enable for matrix A
    input  logic                         wr_en_b,     // Write enable for matrix B
    input  logic [ADDR_WIDTH-1:0]        wr_row_addr, // Row address (0 to N-1)
    input  logic signed [DATA_WIDTH-1:0] wr_data [ARRAY_SIZE],  // Row data (N elements)

    // ---- Control Interface ----
    input  logic                         start,       // Begin matrix multiply
    output logic                         busy,        // Computation in progress
    output logic                         done,        // Results valid

    // ---- Result Interface ----
    input  logic [ADDR_WIDTH-1:0]        rd_row_addr, // Read row address for result
    output logic signed [ACC_WIDTH-1:0]  rd_data [ARRAY_SIZE]   // Result row (N elements)
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    // Controller signals
    logic                  pe_en, pe_clear_acc;
    logic                  skew_load_en, skew_flush;
    logic [CNT_WIDTH-1:0]  cycle_count;

    // Matrix storage (register files)
    logic signed [DATA_WIDTH-1:0] mat_a [ARRAY_SIZE][ARRAY_SIZE]; // Weights
    logic signed [DATA_WIDTH-1:0] mat_b [ARRAY_SIZE][ARRAY_SIZE]; // Activations

    // Skew controller I/O
    logic signed [DATA_WIDTH-1:0] a_feed_in  [ARRAY_SIZE];  // feeds top edge (B columns)
    logic signed [DATA_WIDTH-1:0] b_feed_in  [ARRAY_SIZE];  // feeds left edge (A rows)
    logic signed [DATA_WIDTH-1:0] a_skewed   [ARRAY_SIZE];
    logic signed [DATA_WIDTH-1:0] b_skewed   [ARRAY_SIZE];

    // Result matrix
    logic signed [ACC_WIDTH-1:0]  result_matrix [ARRAY_SIZE][ARRAY_SIZE];

    // =========================================================================
    // Matrix A Register File (Weights)
    // Stored as mat_a[row][col], fed row-by-row through left edge
    // =========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < ARRAY_SIZE; i++)
                for (int j = 0; j < ARRAY_SIZE; j++)
                    mat_a[i][j] <= '0;
        end else if (wr_en_a) begin
            for (int j = 0; j < ARRAY_SIZE; j++)
                mat_a[wr_row_addr][j] <= wr_data[j];
        end
    end

    // =========================================================================
    // Matrix B Register File (Activations)
    // Stored as mat_b[row][col], fed column-by-column through top edge
    // =========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < ARRAY_SIZE; i++)
                for (int j = 0; j < ARRAY_SIZE; j++)
                    mat_b[i][j] <= '0;
        end else if (wr_en_b) begin
            for (int j = 0; j < ARRAY_SIZE; j++)
                mat_b[wr_row_addr][j] <= wr_data[j];
        end
    end

    // =========================================================================
    // Input Feeding Logic
    // During LOAD phase, cycle_count selects which column/row to feed
    //
    // For C = A × B:
    //   a_col (top edge, flows down)   ← columns of B: B[cycle][i]
    //   b_row (left edge, flows right) ← rows of A:    A[i][cycle]
    //
    // This ensures PE[i][j] = sum_k B[k][j] * A[i][k] = sum_k A[i][k]*B[k][j]
    // =========================================================================
    always_comb begin
        for (int i = 0; i < ARRAY_SIZE; i++) begin
            if (cycle_count < CNT_WIDTH'(ARRAY_SIZE)) begin
                // Row cycle_count of B feeds the top edge (flows down through columns)
                a_feed_in[i] = mat_b[cycle_count[ADDR_WIDTH-1:0]][i];
                // Column cycle_count of A feeds the left edge (flows right through rows)
                b_feed_in[i] = mat_a[i][cycle_count[ADDR_WIDTH-1:0]];
            end else begin
                a_feed_in[i] = '0;
                b_feed_in[i] = '0;
            end
        end
    end

    // =========================================================================
    // Input Skew Controllers
    // =========================================================================

    // B column skew (top edge, staggered top-to-bottom)
    input_skew_controller #(
        .ARRAY_SIZE (ARRAY_SIZE),
        .DATA_WIDTH (DATA_WIDTH)
    ) u_skew_a (
        .clk      (clk),
        .rst_n    (rst_n),
        .load_en  (skew_load_en),
        .flush    (skew_flush),
        .data_in  (a_feed_in),
        .data_out (a_skewed)
    );

    // A row skew (left edge, staggered left-to-right)
    input_skew_controller #(
        .ARRAY_SIZE (ARRAY_SIZE),
        .DATA_WIDTH (DATA_WIDTH)
    ) u_skew_b (
        .clk      (clk),
        .rst_n    (rst_n),
        .load_en  (skew_load_en),
        .flush    (skew_flush),
        .data_in  (b_feed_in),
        .data_out (b_skewed)
    );

    // =========================================================================
    // NxN Systolic Array
    // =========================================================================
    systolic_array_4x4 #(
        .ARRAY_SIZE (ARRAY_SIZE),
        .DATA_WIDTH (DATA_WIDTH),
        .ACC_WIDTH  (ACC_WIDTH)
    ) u_array (
        .clk       (clk),
        .rst_n     (rst_n),
        .en        (pe_en),
        .clear_acc (pe_clear_acc),
        .a_col     (a_skewed),
        .b_row     (b_skewed),
        .result    (result_matrix)
    );

    // =========================================================================
    // Controller FSM
    // =========================================================================
    systolic_controller #(
        .ARRAY_SIZE (ARRAY_SIZE)
    ) u_ctrl (
        .clk          (clk),
        .rst_n        (rst_n),
        .start        (start),
        .busy         (busy),
        .done         (done),
        .pe_en        (pe_en),
        .pe_clear_acc (pe_clear_acc),
        .skew_load_en (skew_load_en),
        .skew_flush   (skew_flush),
        .cycle_count  (cycle_count)
    );

    // =========================================================================
    // Result Read Interface
    // =========================================================================
    always_comb begin
        for (int j = 0; j < ARRAY_SIZE; j++) begin
            rd_data[j] = result_matrix[rd_row_addr][j];
        end
    end

endmodule
