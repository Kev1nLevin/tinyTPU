// =============================================================================
// Testbench: tb_systolic_top
// Description: Parameterized verification of NxN Systolic Array Accelerator
//              - Test 1: Identity matrix multiplication
//              - Test 2: Known hand-calculated result
//              - Test 3: Random matrix multiplication with golden model
//              - Test 4: Back-to-back computations
//              - Test 5: Negative number handling (signed arithmetic)
//
//              Set ARRAY_SIZE to test any configuration (4, 8, 16, etc.)
// =============================================================================

`timescale 1ns / 1ps

module tb_systolic_top;

    // -------------------------------------------------------------------------
    // Parameters — CHANGE ARRAY_SIZE HERE
    // -------------------------------------------------------------------------
    parameter ARRAY_SIZE = 8;   // <-- 8x8 array
    parameter DATA_WIDTH = 8;
    parameter ACC_WIDTH  = 32;
    parameter ADDR_WIDTH = $clog2(ARRAY_SIZE);
    parameter CLK_PERIOD = 1.5; // 667 MHz

    // -------------------------------------------------------------------------
    // DUT Signals
    // -------------------------------------------------------------------------
    logic                         clk;
    logic                         rst_n;
    logic                         wr_en_a, wr_en_b;
    logic [ADDR_WIDTH-1:0]        wr_row_addr;
    logic signed [DATA_WIDTH-1:0] wr_data [ARRAY_SIZE];
    logic                         start;
    logic                         busy;
    logic                         done;
    logic [ADDR_WIDTH-1:0]        rd_row_addr;
    logic signed [ACC_WIDTH-1:0]  rd_data [ARRAY_SIZE];

    // -------------------------------------------------------------------------
    // Test matrices
    // -------------------------------------------------------------------------
    logic signed [DATA_WIDTH-1:0] mat_a [ARRAY_SIZE][ARRAY_SIZE];
    logic signed [DATA_WIDTH-1:0] mat_b [ARRAY_SIZE][ARRAY_SIZE];
    logic signed [ACC_WIDTH-1:0]  expected [ARRAY_SIZE][ARRAY_SIZE];

    // Test tracking
    int test_num = 0;
    int pass_count = 0;
    int fail_count = 0;

    // -------------------------------------------------------------------------
    // Clock generation
    // -------------------------------------------------------------------------
    initial clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // -------------------------------------------------------------------------
    // DUT instantiation
    // -------------------------------------------------------------------------
    systolic_top #(
        .ARRAY_SIZE (ARRAY_SIZE),
        .DATA_WIDTH (DATA_WIDTH),
        .ACC_WIDTH  (ACC_WIDTH)
    ) dut (
        .clk         (clk),
        .rst_n       (rst_n),
        .wr_en_a     (wr_en_a),
        .wr_en_b     (wr_en_b),
        .wr_row_addr (wr_row_addr),
        .wr_data     (wr_data),
        .start       (start),
        .busy        (busy),
        .done        (done),
        .rd_row_addr (rd_row_addr),
        .rd_data     (rd_data)
    );

    // -------------------------------------------------------------------------
    // Tasks
    // -------------------------------------------------------------------------

    task automatic do_reset();
        rst_n   <= 1'b0;
        start   <= 1'b0;
        wr_en_a <= 1'b0;
        wr_en_b <= 1'b0;
        wr_row_addr <= '0;
        rd_row_addr <= '0;
        for (int i = 0; i < ARRAY_SIZE; i++) wr_data[i] <= '0;
        repeat (5) @(posedge clk);
        rst_n <= 1'b1;
        repeat (2) @(posedge clk);
    endtask

    task automatic load_matrix_a(input logic signed [DATA_WIDTH-1:0] mat [ARRAY_SIZE][ARRAY_SIZE]);
        for (int row = 0; row < ARRAY_SIZE; row++) begin
            @(posedge clk);
            wr_en_a     <= 1'b1;
            wr_row_addr <= ADDR_WIDTH'(row);
            for (int col = 0; col < ARRAY_SIZE; col++)
                wr_data[col] <= mat[row][col];
        end
        @(posedge clk);
        wr_en_a <= 1'b0;
    endtask

    task automatic load_matrix_b(input logic signed [DATA_WIDTH-1:0] mat [ARRAY_SIZE][ARRAY_SIZE]);
        for (int row = 0; row < ARRAY_SIZE; row++) begin
            @(posedge clk);
            wr_en_b     <= 1'b1;
            wr_row_addr <= ADDR_WIDTH'(row);
            for (int col = 0; col < ARRAY_SIZE; col++)
                wr_data[col] <= mat[row][col];
        end
        @(posedge clk);
        wr_en_b <= 1'b0;
    endtask

    task automatic run_computation();
        @(posedge clk);
        start <= 1'b1;
        @(posedge clk);
        start <= 1'b0;

        fork
            begin
                wait (done);
            end
            begin
                repeat (200) @(posedge clk);
                $error("TIMEOUT: Computation did not complete in 200 cycles!");
            end
        join_any
        disable fork;
        @(posedge clk);
    endtask

    // Golden model: software matrix multiply
    task automatic golden_matmul(
        input  logic signed [DATA_WIDTH-1:0] a [ARRAY_SIZE][ARRAY_SIZE],
        input  logic signed [DATA_WIDTH-1:0] b [ARRAY_SIZE][ARRAY_SIZE],
        output logic signed [ACC_WIDTH-1:0]  c [ARRAY_SIZE][ARRAY_SIZE]
    );
        for (int i = 0; i < ARRAY_SIZE; i++)
            for (int j = 0; j < ARRAY_SIZE; j++) begin
                c[i][j] = 0;
                for (int k = 0; k < ARRAY_SIZE; k++)
                    c[i][j] = c[i][j] + (ACC_WIDTH'(a[i][k]) * ACC_WIDTH'(b[k][j]));
            end
    endtask

    // Check results
    task automatic check_results(input string test_name);
        logic all_pass;
        all_pass = 1;

        $display("\n--- %s ---", test_name);

        for (int i = 0; i < ARRAY_SIZE; i++) begin
            rd_row_addr <= ADDR_WIDTH'(i);
            @(posedge clk);
            @(negedge clk);

            for (int j = 0; j < ARRAY_SIZE; j++) begin
                if (rd_data[j] !== expected[i][j]) begin
                    $error("  MISMATCH C[%0d][%0d]: expected=%0d, got=%0d",
                           i, j, expected[i][j], rd_data[j]);
                    all_pass = 0;
                end
            end
        end

        if (all_pass) begin
            $display("  >> %s PASSED", test_name);
            pass_count++;
        end else begin
            $display("  >> %s FAILED", test_name);
            fail_count++;
        end
    endtask

    // -------------------------------------------------------------------------
    // Test Sequence
    // -------------------------------------------------------------------------
    initial begin
        $display("==========================================================");
        $display("  %0dx%0d Systolic Array - Neural Network MAC Accelerator", ARRAY_SIZE, ARRAY_SIZE);
        $display("  Verification Testbench");
        $display("==========================================================");

        do_reset();

        // TEST 1: Identity Matrix (A * I = A)
        test_num = 1;
        $display("\n========== TEST %0d: Identity Matrix (%0dx%0d) ==========", test_num, ARRAY_SIZE, ARRAY_SIZE);

        for (int i = 0; i < ARRAY_SIZE; i++)
            for (int j = 0; j < ARRAY_SIZE; j++)
                mat_a[i][j] = DATA_WIDTH'((i * ARRAY_SIZE + j + 1) % 120);

        for (int i = 0; i < ARRAY_SIZE; i++)
            for (int j = 0; j < ARRAY_SIZE; j++)
                mat_b[i][j] = (i == j) ? 8'sd1 : 8'sd0;

        golden_matmul(mat_a, mat_b, expected);
        load_matrix_a(mat_a);
        load_matrix_b(mat_b);
        run_computation();
        check_results("Identity Multiply");

        // TEST 2: Known Small Values
        test_num = 2;
        $display("\n========== TEST %0d: Known Values ==========", test_num);
        do_reset();

        for (int i = 0; i < ARRAY_SIZE; i++)
            for (int j = 0; j < ARRAY_SIZE; j++) begin
                mat_a[i][j] = DATA_WIDTH'((i + j + 1) % 10);
                mat_b[i][j] = DATA_WIDTH'((i * 2 + j) % 8);
            end

        golden_matmul(mat_a, mat_b, expected);
        load_matrix_a(mat_a);
        load_matrix_b(mat_b);
        run_computation();
        check_results("Known Values");

        // TEST 3: Random Matrices
        test_num = 3;
        $display("\n========== TEST %0d: Random Matrices ==========", test_num);
        do_reset();

        for (int i = 0; i < ARRAY_SIZE; i++)
            for (int j = 0; j < ARRAY_SIZE; j++) begin
                mat_a[i][j] = $urandom_range(0, 15);
                mat_b[i][j] = $urandom_range(0, 15);
            end

        golden_matmul(mat_a, mat_b, expected);
        load_matrix_a(mat_a);
        load_matrix_b(mat_b);
        run_computation();
        check_results("Random Matrices");

        // TEST 4: Back-to-back (no reset)
        test_num = 4;
        $display("\n========== TEST %0d: Back-to-Back ==========", test_num);

        for (int i = 0; i < ARRAY_SIZE; i++)
            for (int j = 0; j < ARRAY_SIZE; j++) begin
                mat_a[i][j] = $urandom_range(1, 10);
                mat_b[i][j] = $urandom_range(1, 10);
            end

        golden_matmul(mat_a, mat_b, expected);
        load_matrix_a(mat_a);
        load_matrix_b(mat_b);
        run_computation();
        check_results("Back-to-Back");

        // TEST 5: Signed (Negative) Numbers
        test_num = 5;
        $display("\n========== TEST %0d: Signed Numbers ==========", test_num);
        do_reset();

        for (int i = 0; i < ARRAY_SIZE; i++)
            for (int j = 0; j < ARRAY_SIZE; j++) begin
                mat_a[i][j] = $signed($urandom_range(0, 30)) - 8'sd15;
                mat_b[i][j] = $signed($urandom_range(0, 30)) - 8'sd15;
            end

        golden_matmul(mat_a, mat_b, expected);
        load_matrix_a(mat_a);
        load_matrix_b(mat_b);
        run_computation();
        check_results("Signed Numbers");

        // SUMMARY
        $display("\n==========================================================");
        $display("  TEST SUMMARY (%0dx%0d Array)", ARRAY_SIZE, ARRAY_SIZE);
        $display("  Passed: %0d / %0d", pass_count, pass_count + fail_count);
        $display("  Failed: %0d / %0d", fail_count, pass_count + fail_count);
        if (fail_count == 0)
            $display("  >>> ALL TESTS PASSED <<<");
        else
            $display("  >>> SOME TESTS FAILED <<<");
        $display("==========================================================\n");

        $finish;
    end

    // Waveform dump
    initial begin
        $dumpfile("systolic_top.vcd");
        $dumpvars(0, tb_systolic_top);
    end

    // Timeout watchdog
    initial begin
        #100000;
        $error("GLOBAL TIMEOUT: Simulation exceeded 100000 time units");
        $finish;
    end

endmodule
