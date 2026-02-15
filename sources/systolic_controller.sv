// =============================================================================
// Module: systolic_controller
// Description: FSM Controller for 4x4 Systolic Array
//              Orchestrates the matrix multiplication sequence:
//              1. IDLE    -> Wait for start signal
//              2. LOAD    -> Feed skewed inputs into the array (N + N-1 cycles)
//              3. DRAIN   -> Wait for results to propagate
//              4. DONE    -> Signal completion, results are valid
//
//              For a 4x4 array, full computation takes:
//              - 4 cycles to feed data + 3 cycles for skew propagation
//              = 7 cycles total (ARRAY_SIZE + ARRAY_SIZE - 1)
// =============================================================================

module systolic_controller #(
    parameter ARRAY_SIZE = 4
)(
    input  logic       clk,
    input  logic       rst_n,

    // Control interface
    input  logic       start,         // Pulse to begin computation
    output logic       busy,          // High during computation
    output logic       done,          // Pulse when results are valid

    // Control signals to datapath
    output logic       pe_en,         // Enable PEs
    output logic       pe_clear_acc,  // Clear PE accumulators
    output logic       skew_load_en,  // Enable skew controller loading
    output logic       skew_flush,    // Flush skew registers

    // Cycle counter (exposed for input muxing)
    output logic [3:0] cycle_count
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

    // Total cycles needed: feed all N columns/rows + propagation through array
    localparam FEED_CYCLES  = ARRAY_SIZE;                   // 4 cycles to load
    localparam DRAIN_CYCLES = ARRAY_SIZE - 1;               // 3 cycles to drain
    localparam TOTAL_CYCLES = FEED_CYCLES + DRAIN_CYCLES;   // 7 total

    logic [3:0] counter;

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
                S_LOAD:  counter <= counter + 4'd1;
                S_DRAIN: counter <= counter + 4'd1;
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
            S_IDLE:  if (start)                          next_state = S_CLEAR;
            S_CLEAR:                                     next_state = S_LOAD;
            S_LOAD:  if (counter == FEED_CYCLES - 1)     next_state = S_DRAIN;
            S_DRAIN: if (counter == TOTAL_CYCLES - 1)    next_state = S_DONE;
            S_DONE:                                      next_state = S_IDLE;
            default:                                     next_state = S_IDLE;
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
