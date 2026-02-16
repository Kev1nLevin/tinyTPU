// =============================================================================
// Module: systolic_controller
// Description: FSM Controller for NxN Systolic Array
//              Orchestrates the matrix multiplication sequence:
//              1. IDLE    -> Wait for start signal
//              2. CLEAR   -> Clear accumulators and skew registers
//              3. LOAD    -> Feed skewed inputs (N cycles)
//              4. DRAIN   -> Wait for full propagation (2*(N-1) cycles)
//              5. DONE    -> Signal completion, results are valid
//
//              Total computation: N + 2*(N-1) = 3N - 2 cycles
//              For 4x4: 10 cycles.  For 8x8: 22 cycles.
//
//              The drain must be 2*(N-1) because:
//              - N-1 cycles for the skew controller to flush channel N-1
//              - N-1 cycles for that data to propagate to PE[N-1][N-1]
//
//              Fully parameterized — works for any ARRAY_SIZE (4, 8, 16, etc.)
// =============================================================================

module systolic_controller #(
    parameter ARRAY_SIZE = 4,
    parameter CNT_WIDTH  = $clog2(3*ARRAY_SIZE)  // bits needed for 3N-2 count
)(
    input  logic                  clk,
    input  logic                  rst_n,

    // Control interface
    input  logic                  start,         // Pulse to begin computation
    output logic                  busy,          // High during computation
    output logic                  done,          // Pulse when results are valid

    // Control signals to datapath
    output logic                  pe_en,         // Enable PEs
    output logic                  pe_clear_acc,  // Clear PE accumulators
    output logic                  skew_load_en,  // Enable skew controller loading
    output logic                  skew_flush,    // Flush skew registers

    // Cycle counter (exposed for input muxing)
    output logic [CNT_WIDTH-1:0]  cycle_count
);

    // -------------------------------------------------------------------------
    // FSM State encoding
    // -------------------------------------------------------------------------
    typedef enum logic [2:0] {
        S_IDLE  = 3'b000,
        S_CLEAR = 3'b001,
        S_LOAD  = 3'b010,
        S_DRAIN = 3'b011,
        S_DONE  = 3'b100
    } state_t;

    state_t state, next_state;

    // Total cycles needed
    localparam FEED_CYCLES  = ARRAY_SIZE;                       // N cycles to load
    localparam DRAIN_CYCLES = 2 * (ARRAY_SIZE - 1);             // 2*(N-1) cycles to drain
    localparam TOTAL_CYCLES = FEED_CYCLES + DRAIN_CYCLES;       // 3N-2 total

    logic [CNT_WIDTH-1:0] counter;

    // -------------------------------------------------------------------------
    // State register
    // -------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= S_IDLE;
        else
            state <= next_state;
    end

    // -------------------------------------------------------------------------
    // Counter
    // -------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= '0;
        end else begin
            case (state)
                S_CLEAR: counter <= '0;
                S_LOAD:  counter <= counter + CNT_WIDTH'(1);
                S_DRAIN: counter <= counter + CNT_WIDTH'(1);
                default: counter <= '0;
            endcase
        end
    end

    assign cycle_count = counter;

    // -------------------------------------------------------------------------
    // Next state logic
    // -------------------------------------------------------------------------
    always_comb begin
        next_state = state;
        case (state)
            S_IDLE:  if (start)                                    next_state = S_CLEAR;
            S_CLEAR:                                               next_state = S_LOAD;
            S_LOAD:  if (counter == CNT_WIDTH'(FEED_CYCLES - 1))   next_state = S_DRAIN;
            S_DRAIN: if (counter == CNT_WIDTH'(TOTAL_CYCLES - 1))  next_state = S_DONE;
            S_DONE:                                                next_state = S_IDLE;
            default:                                               next_state = S_IDLE;
        endcase
    end

    // -------------------------------------------------------------------------
    // Output logic
    // -------------------------------------------------------------------------
    assign busy         = (state != S_IDLE) && (state != S_DONE);
    assign done         = (state == S_DONE);
    assign pe_en        = (state == S_LOAD) || (state == S_DRAIN);
    assign pe_clear_acc = (state == S_CLEAR);
    assign skew_load_en = (state == S_LOAD);
    assign skew_flush   = (state == S_CLEAR);

endmodule
