// =============================================================================
// Module: systolic_controller
// Description: FSM Controller for NxN Systolic Array (Production)
//              Orchestrates the matrix multiplication sequence:
//              1. IDLE         → Wait for start signal
//              2. CLEAR        → Clear accumulators (skipped if acc_mode=1)
//              3. LOAD         → Feed skewed inputs (N cycles)
//              4. DRAIN        → Wait for propagation (2*(N-1) + MAC_LAT-1)
//              5. DRAIN_RESULT → Copy results through activation to SRAM (N cycles)
//              6. DONE         → Signal completion
//
//              New features:
//              - acc_mode: skip CLEAR for tiling/accumulation across tiles
//              - DRAIN_RESULT phase: registered result readout for timing
// =============================================================================

module systolic_controller #(
    parameter ARRAY_SIZE  = 32,
    parameter MAC_LATENCY = 2,
    parameter CNT_WIDTH   = $clog2(3*ARRAY_SIZE + MAC_LATENCY)
)(
    input  logic                  clk,
    input  logic                  rst_n,

    // Control interface
    input  logic                  start,
    input  logic                  acc_mode,      // 1 = skip accumulator clear (tiling)
    output logic                  busy,
    output logic                  done,

    // Control signals to datapath
    output logic                  pe_en,
    output logic                  pe_clear_acc,
    output logic                  skew_load_en,
    output logic                  skew_flush,

    // Result drain control
    output logic                  drain_result_en,    // high during DRAIN_RESULT
    output logic [CNT_WIDTH-1:0]  drain_row,          // which row to drain

    // Cycle counter (exposed for input muxing)
    output logic [CNT_WIDTH-1:0]  cycle_count
);

    // -------------------------------------------------------------------------
    // FSM State encoding
    // -------------------------------------------------------------------------
    typedef enum logic [2:0] {
        S_IDLE         = 3'b000,
        S_CLEAR        = 3'b001,
        S_LOAD         = 3'b010,
        S_DRAIN        = 3'b011,
        S_DRAIN_RESULT = 3'b100,
        S_DONE         = 3'b101
    } state_t;

    state_t state, next_state;

    // Cycle budget
    localparam FEED_CYCLES  = ARRAY_SIZE;
    localparam DRAIN_CYCLES = 2 * (ARRAY_SIZE - 1) + (MAC_LATENCY - 1);
    localparam TOTAL_CYCLES = FEED_CYCLES + DRAIN_CYCLES;

    logic [CNT_WIDTH-1:0] counter;
    logic [CNT_WIDTH-1:0] drain_counter;

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
    // Main counter (for LOAD + DRAIN phases)
    // -------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= '0;
        end else begin
            case (state)
                S_CLEAR:        counter <= '0;
                S_LOAD:         counter <= counter + CNT_WIDTH'(1);
                S_DRAIN:        counter <= counter + CNT_WIDTH'(1);
                default:        counter <= '0;
            endcase
        end
    end

    assign cycle_count = counter;

    // -------------------------------------------------------------------------
    // Drain result counter (for DRAIN_RESULT phase)
    // -------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            drain_counter <= '0;
        end else begin
            if (state == S_DRAIN_RESULT)
                drain_counter <= drain_counter + CNT_WIDTH'(1);
            else
                drain_counter <= '0;
        end
    end

    assign drain_row = drain_counter;

    // -------------------------------------------------------------------------
    // Next state logic
    // -------------------------------------------------------------------------
    always_comb begin
        next_state = state;
        case (state)
            S_IDLE:
                if (start)
                    next_state = S_CLEAR;

            S_CLEAR:
                // If acc_mode, skip clearing and go straight to LOAD
                // Still spend 1 cycle here for skew flush
                next_state = S_LOAD;

            S_LOAD:
                if (counter == CNT_WIDTH'(FEED_CYCLES - 1))
                    next_state = S_DRAIN;

            S_DRAIN:
                if (counter == CNT_WIDTH'(TOTAL_CYCLES - 1))
                    next_state = S_DRAIN_RESULT;

            S_DRAIN_RESULT:
                if (drain_counter == CNT_WIDTH'(ARRAY_SIZE - 1))
                    next_state = S_DONE;

            S_DONE:
                next_state = S_IDLE;

            default:
                next_state = S_IDLE;
        endcase
    end

    // -------------------------------------------------------------------------
    // Output logic
    // -------------------------------------------------------------------------
    assign busy           = (state != S_IDLE) && (state != S_DONE);
    assign done           = (state == S_DONE);
    assign pe_en          = (state == S_LOAD) || (state == S_DRAIN);
    assign pe_clear_acc   = (state == S_CLEAR) && !acc_mode;
    assign skew_load_en   = (state == S_LOAD);
    assign skew_flush     = (state == S_CLEAR);
    assign drain_result_en = (state == S_DRAIN_RESULT);

    // =========================================================================
    // SVA — Assertions
    // =========================================================================
    // synthesis translate_off
    property p_done_is_pulse;
        @(posedge clk) disable iff (!rst_n)
        done |=> !done;
    endproperty
    assert property (p_done_is_pulse)
        else $error("CTRL: done was not a single-cycle pulse");

    property p_busy_after_start;
        @(posedge clk) disable iff (!rst_n)
        start && (state == S_IDLE) |=> busy;
    endproperty
    assert property (p_busy_after_start)
        else $error("CTRL: busy did not assert after start");

    property p_no_start_during_busy;
        @(posedge clk) disable iff (!rst_n)
        start |-> (state == S_IDLE);
    endproperty
    // This is an assumption — the wrapper must enforce it
    // assert property (p_no_start_during_busy);
    // synthesis translate_on

endmodule
