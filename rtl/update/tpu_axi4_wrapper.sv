// =============================================================================
// Module: tpu_axi4_wrapper
// Description: AXI4 Memory-Mapped Slave Interface for TPU (Production)
//              Bridges an AXI4 master (RV64 CPU) to the systolic array top.
//
//              Production enhancements:
//              - WSTRB (write strobe) handling for CTRL register
//              - SLVERR responses for invalid addresses and writes during busy
//              - Busy protection: rejects start if TPU is computing
//              - Performance counter read-back via MMIO
//              - Accumulate mode (acc_mode) CTRL bit for tiling
//              - Bias register write path
//              - Activation function select via CTRL
//              - Level-sensitive interrupt with clear-on-start
//
//              Memory Map (byte addresses, 64-bit AXI data bus):
//              ┌──────────────┬──────────┬─────────────────────────────┐
//              │ Region       │ Offset   │ Description                  │
//              ├──────────────┼──────────┼─────────────────────────────┤
//              │ CTRL         │ 0x0000   │ Control/Status register      │
//              │ MAT_A        │ 0x1000   │ Weight matrix (WO, 32 rows)  │
//              │ MAT_B        │ 0x2000   │ Activation matrix (WO, rows) │
//              │ RESULT       │ 0x3000   │ Result matrix (RO, 32 rows)  │
//              │ PERF         │ 0x4000   │ Performance counters (RO)    │
//              │ BIAS         │ 0x5000   │ Bias register file (WO)      │
//              └──────────────┴──────────┴─────────────────────────────┘
//
//              CTRL Register (write):
//              [0]   start     — pulse, triggers computation (ignored if busy)
//              [1]   reserved
//              [2]   acc_mode  — 1 = accumulate (don't clear), 0 = normal
//              [3]   irq_en   — 1 = enable interrupt on done
//              [6:4] act_func — activation: 000=none, 001=relu, 010=gelu
//              [7]   bias_en  — 1 = add bias before activation
//
//              CTRL Register (read):
//              [0]   busy
//              [1]   done
//              [2]   acc_mode
//              [3]   irq_en
//              [6:4] act_func
//              [7]   bias_en
// =============================================================================

module tpu_axi4_wrapper #(
    parameter AXI_DATA_WIDTH = 64,
    parameter AXI_ADDR_WIDTH = 20,
    parameter ARRAY_SIZE     = 32,
    parameter DATA_WIDTH     = 16,
    parameter ACC_WIDTH      = 32,
    parameter AXI_ID_WIDTH   = 4
)(
    input  logic                          clk,
    input  logic                          rst_n,

    // AXI4 Slave Interface — Write Address Channel
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_awaddr,
    input  logic [7:0]                    s_axi_awlen,
    input  logic [2:0]                    s_axi_awsize,
    input  logic [1:0]                    s_axi_awburst,
    input  logic                          s_axi_awvalid,
    output logic                          s_axi_awready,

    // AXI4 Write Data Channel
    input  logic [AXI_DATA_WIDTH-1:0]     s_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0]   s_axi_wstrb,
    input  logic                          s_axi_wlast,
    input  logic                          s_axi_wvalid,
    output logic                          s_axi_wready,

    // AXI4 Write Response Channel
    output logic [AXI_ID_WIDTH-1:0]       s_axi_bid,
    output logic [1:0]                    s_axi_bresp,
    output logic                          s_axi_bvalid,
    input  logic                          s_axi_bready,

    // AXI4 Read Address Channel
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_araddr,
    input  logic [7:0]                    s_axi_arlen,
    input  logic [2:0]                    s_axi_arsize,
    input  logic [1:0]                    s_axi_arburst,
    input  logic                          s_axi_arvalid,
    output logic                          s_axi_arready,

    // AXI4 Read Data Channel
    output logic [AXI_ID_WIDTH-1:0]       s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]     s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic                          s_axi_rvalid,
    input  logic                          s_axi_rready,

    // Interrupt
    output logic                          irq
);

    // =========================================================================
    // Internal constants
    // =========================================================================
    localparam ADDR_W  = $clog2(ARRAY_SIZE);
    localparam AXI_STRB_W = AXI_DATA_WIDTH / 8;

    // Region decode from address bits [15:12]
    localparam [3:0] REGION_CTRL   = 4'h0;
    localparam [3:0] REGION_MAT_A  = 4'h1;
    localparam [3:0] REGION_MAT_B  = 4'h2;
    localparam [3:0] REGION_RESULT = 4'h3;
    localparam [3:0] REGION_PERF   = 4'h4;
    localparam [3:0] REGION_BIAS   = 4'h5;

    // How many AXI beats per matrix row
    localparam BEATS_PER_ROW_IN  = (ARRAY_SIZE * DATA_WIDTH) / AXI_DATA_WIDTH; // 32*16/64=8
    localparam BEATS_PER_ROW_OUT = (ARRAY_SIZE * ACC_WIDTH)  / AXI_DATA_WIDTH; // 32*32/64=16

    // =========================================================================
    // Control registers
    // =========================================================================
    logic        tpu_start_r;
    logic        ctrl_acc_mode;
    logic        ctrl_irq_en;
    logic [2:0]  ctrl_act_func;
    logic        ctrl_bias_en;
    logic        ctrl_done;

    // TPU signals
    logic        tpu_busy;
    logic        tpu_done;
    logic signed [ACC_WIDTH-1:0] rd_data [ARRAY_SIZE];
    logic        rd_valid;
    logic [31:0] perf_total, perf_compute, perf_idle;

    // =========================================================================
    // Systolic Top Instance
    // =========================================================================
    logic        wr_en_a, wr_en_b;
    logic [ADDR_W-1:0] wr_row_addr;
    logic signed [DATA_WIDTH-1:0] wr_data_vec [ARRAY_SIZE];
    logic [ADDR_W-1:0] rd_row_addr;
    logic        rd_en;

    // Bias write
    logic        bias_wr_en_r;
    logic [ADDR_W-1:0] bias_wr_addr_r;
    logic [ACC_WIDTH-1:0] bias_wr_data_r;

    systolic_top #(
        .ARRAY_SIZE        (ARRAY_SIZE),
        .DATA_WIDTH        (DATA_WIDTH),
        .ACC_WIDTH         (ACC_WIDTH),
        .MAC_LATENCY       (2),
        .ENABLE_DOUBLE_BUF (1)
    ) u_systolic_top (
        .clk                (clk),
        .rst_n              (rst_n),
        .tpu_start          (tpu_start_r),
        .acc_mode           (ctrl_acc_mode),
        .tpu_busy           (tpu_busy),
        .tpu_done           (tpu_done),
        .act_func           (ctrl_act_func),
        .wr_en_a            (wr_en_a),
        .wr_en_b            (wr_en_b),
        .wr_row_addr        (wr_row_addr),
        .wr_data            (wr_data_vec),
        .rd_row_addr        (rd_row_addr),
        .rd_en              (rd_en),
        .rd_data            (rd_data),
        .rd_valid           (rd_valid),
        .bias_wr_en         (bias_wr_en_r),
        .bias_wr_addr       (bias_wr_addr_r),
        .bias_wr_data       (bias_wr_data_r),
        .bias_en            (ctrl_bias_en),
        .perf_total_cycles  (perf_total),
        .perf_compute_cycles(perf_compute),
        .perf_idle_cycles   (perf_idle)
    );

    // =========================================================================
    // Done flag (sticky until next start) & interrupt
    // =========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            ctrl_done <= 1'b0;
        else if (tpu_done)
            ctrl_done <= 1'b1;
        else if (tpu_start_r)
            ctrl_done <= 1'b0;
    end

    // Interrupt: level-sensitive, active when done and irq enabled
    assign irq = ctrl_done & ctrl_irq_en;

    // =========================================================================
    // Write FSM (includes start pulse generation — single driver for all regs)
    // =========================================================================
    typedef enum logic [1:0] {
        WR_IDLE    = 2'b00,
        WR_DATA    = 2'b01,
        WR_RESP    = 2'b10
    } wr_state_t;

    wr_state_t wr_state;

    logic [AXI_ADDR_WIDTH-1:0] wr_addr_reg;
    logic [AXI_ID_WIDTH-1:0]   wr_id_reg;
    logic [7:0]                wr_len_reg;
    logic [7:0]                wr_beat_cnt;
    logic [3:0]                wr_region;
    logic                      wr_error;
    logic                      start_req;  // set on CTRL write, consumed next cycle

    assign wr_region = wr_addr_reg[15:12];

    // Determine write error
    always_comb begin
        wr_error = 1'b0;
        case (wr_region)
            REGION_CTRL:   wr_error = 1'b0;
            REGION_MAT_A:  wr_error = tpu_busy;  // Can't write during compute (single buf would corrupt)
            REGION_MAT_B:  wr_error = tpu_busy;
            REGION_BIAS:   wr_error = 1'b0;
            REGION_RESULT: wr_error = 1'b1;       // Results are read-only
            REGION_PERF:   wr_error = 1'b1;       // Perf counters are read-only
            default:       wr_error = 1'b1;       // Unknown region
        endcase
    end

    // Beat address within region
    logic [AXI_ADDR_WIDTH-1:0] wr_beat_addr;
    assign wr_beat_addr = wr_addr_reg + {{(AXI_ADDR_WIDTH-8){1'b0}}, wr_beat_cnt} * (AXI_DATA_WIDTH/8);

    // Row and beat-within-row decode for matrix writes
    // Each row = BEATS_PER_ROW_IN beats; row_addr = beat_addr[high bits]
    logic [ADDR_W-1:0] wr_mat_row;
    logic [$clog2(BEATS_PER_ROW_IN)-1:0] wr_mat_beat;

    assign wr_mat_row  = wr_beat_addr[$clog2(BEATS_PER_ROW_IN)+$clog2(AXI_DATA_WIDTH/8)+ADDR_W-1 : $clog2(BEATS_PER_ROW_IN)+$clog2(AXI_DATA_WIDTH/8)];
    assign wr_mat_beat = wr_beat_addr[$clog2(BEATS_PER_ROW_IN)+$clog2(AXI_DATA_WIDTH/8)-1 : $clog2(AXI_DATA_WIDTH/8)];

    // Write data assembly: accumulate AXI beats into a row buffer
    logic [DATA_WIDTH-1:0] wr_row_buf [ARRAY_SIZE];
    logic wr_row_complete;

    assign wr_row_complete = (wr_mat_beat == BEATS_PER_ROW_IN[$clog2(BEATS_PER_ROW_IN)-1:0] - 1);

    // Unified write FSM + start pulse generation (single always_ff — no multi-driver)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_state      <= WR_IDLE;
            wr_addr_reg   <= '0;
            wr_id_reg     <= '0;
            wr_len_reg    <= '0;
            wr_beat_cnt   <= '0;
            wr_en_a       <= 1'b0;
            wr_en_b       <= 1'b0;
            ctrl_acc_mode <= 1'b0;
            ctrl_irq_en   <= 1'b0;
            ctrl_act_func <= 3'b000;
            ctrl_bias_en  <= 1'b0;
            bias_wr_en_r   <= 1'b0;
            bias_wr_addr_r <= '0;
            bias_wr_data_r <= '0;
            tpu_start_r    <= 1'b0;
            start_req      <= 1'b0;
        end else begin
            // ---- Start pulse: convert start_req into 1-cycle tpu_start_r ----
            tpu_start_r <= start_req;
            if (start_req)
                start_req <= 1'b0;

            // ---- Default: deassert single-cycle write enables ----
            wr_en_a      <= 1'b0;
            wr_en_b      <= 1'b0;
            bias_wr_en_r <= 1'b0;

            case (wr_state)
                WR_IDLE: begin
                    if (s_axi_awvalid) begin
                        wr_addr_reg <= s_axi_awaddr;
                        wr_id_reg   <= s_axi_awid;
                        wr_len_reg  <= s_axi_awlen;
                        wr_beat_cnt <= '0;
                        wr_state    <= WR_DATA;
                    end
                end

                WR_DATA: begin
                    if (s_axi_wvalid && !wr_error) begin
                        case (wr_region)
                            REGION_CTRL: begin
                                // Byte-lane-aware CTRL write
                                if (s_axi_wstrb[0]) begin
                                    if (s_axi_wdata[0] && !tpu_busy)
                                        start_req <= 1'b1;
                                    ctrl_acc_mode <= s_axi_wdata[2];
                                    ctrl_irq_en   <= s_axi_wdata[3];
                                    ctrl_act_func <= s_axi_wdata[6:4];
                                    ctrl_bias_en  <= s_axi_wdata[7];
                                end
                            end

                            REGION_MAT_A, REGION_MAT_B: begin
                                // Unpack 64-bit AXI data into row buffer positions
                                for (int b = 0; b < AXI_DATA_WIDTH/DATA_WIDTH; b++) begin
                                    automatic int idx = int'(wr_mat_beat) * (AXI_DATA_WIDTH/DATA_WIDTH) + b;
                                    if (idx < ARRAY_SIZE)
                                        wr_row_buf[idx] <= s_axi_wdata[b*DATA_WIDTH +: DATA_WIDTH];
                                end

                                // On last beat of row, commit to SRAM
                                if (wr_row_complete) begin
                                    wr_row_addr <= wr_mat_row;
                                    if (wr_region == REGION_MAT_A)
                                        wr_en_a <= 1'b1;
                                    else
                                        wr_en_b <= 1'b1;
                                end
                            end

                            REGION_BIAS: begin
                                // Each beat writes one FP32 bias value
                                bias_wr_en_r   <= 1'b1;
                                bias_wr_addr_r <= wr_beat_addr[ADDR_W+$clog2(AXI_DATA_WIDTH/8)-1 : $clog2(AXI_DATA_WIDTH/8)];
                                bias_wr_data_r <= s_axi_wdata[ACC_WIDTH-1:0];
                            end

                            default: ;  // error regions handled by wr_error
                        endcase

                        wr_beat_cnt <= wr_beat_cnt + 8'd1;

                        if (s_axi_wlast)
                            wr_state <= WR_RESP;
                    end else if (s_axi_wvalid && wr_error) begin
                        // Consume beat but discard data
                        wr_beat_cnt <= wr_beat_cnt + 8'd1;
                        if (s_axi_wlast)
                            wr_state <= WR_RESP;
                    end
                end

                WR_RESP: begin
                    if (s_axi_bready) begin
                        wr_state <= WR_IDLE;
                    end
                end

                default: wr_state <= WR_IDLE;
            endcase
        end
    end

    // Connect row buffer to systolic_top write data port
    always_comb begin
        for (int i = 0; i < ARRAY_SIZE; i++)
            wr_data_vec[i] = wr_row_buf[i];
    end

    // Write channel outputs
    assign s_axi_awready = (wr_state == WR_IDLE);
    assign s_axi_wready  = (wr_state == WR_DATA);
    assign s_axi_bvalid  = (wr_state == WR_RESP);
    assign s_axi_bid     = wr_id_reg;
    assign s_axi_bresp   = wr_error ? 2'b10 : 2'b00;  // SLVERR or OKAY

    // =========================================================================
    // Read FSM
    // =========================================================================
    typedef enum logic [1:0] {
        RD_IDLE    = 2'b00,
        RD_WAIT    = 2'b01,   // wait for SRAM read latency
        RD_DATA    = 2'b10
    } rd_state_t;

    rd_state_t rd_state;

    logic [AXI_ADDR_WIDTH-1:0] rd_addr_reg;
    logic [AXI_ID_WIDTH-1:0]   rd_id_reg;
    logic [7:0]                rd_len_reg;
    logic [7:0]                rd_beat_cnt;
    logic [3:0]                rd_region;
    logic                      rd_error;

    assign rd_region = rd_addr_reg[15:12];

    always_comb begin
        rd_error = 1'b0;
        case (rd_region)
            REGION_CTRL:   rd_error = 1'b0;
            REGION_RESULT: rd_error = 1'b0;
            REGION_PERF:   rd_error = 1'b0;
            REGION_MAT_A:  rd_error = 1'b1;  // write-only
            REGION_MAT_B:  rd_error = 1'b1;  // write-only
            REGION_BIAS:   rd_error = 1'b1;  // write-only
            default:       rd_error = 1'b1;  // unknown
        endcase
    end

    logic [AXI_ADDR_WIDTH-1:0] rd_beat_addr;
    assign rd_beat_addr = rd_addr_reg + {{(AXI_ADDR_WIDTH-8){1'b0}}, rd_beat_cnt} * (AXI_DATA_WIDTH/8);

    // Result row and beat decode
    logic [ADDR_W-1:0] rd_result_row;
    logic [$clog2(BEATS_PER_ROW_OUT)-1:0] rd_result_beat;

    assign rd_result_row  = rd_beat_addr[$clog2(BEATS_PER_ROW_OUT)+$clog2(AXI_DATA_WIDTH/8)+ADDR_W-1 : $clog2(BEATS_PER_ROW_OUT)+$clog2(AXI_DATA_WIDTH/8)];
    assign rd_result_beat = rd_beat_addr[$clog2(BEATS_PER_ROW_OUT)+$clog2(AXI_DATA_WIDTH/8)-1 : $clog2(AXI_DATA_WIDTH/8)];

    // Read data mux
    logic [AXI_DATA_WIDTH-1:0] rd_data_mux;

    always_comb begin
        rd_data_mux = '0;
        case (rd_region)
            REGION_CTRL: begin
                rd_data_mux = '0;
                rd_data_mux[0] = tpu_busy;
                rd_data_mux[1] = ctrl_done;
                rd_data_mux[2] = ctrl_acc_mode;
                rd_data_mux[3] = ctrl_irq_en;
                rd_data_mux[6:4] = ctrl_act_func;
                rd_data_mux[7] = ctrl_bias_en;
            end

            REGION_RESULT: begin
                // Extract 64-bit slice from the read data row
                for (int b = 0; b < AXI_DATA_WIDTH/ACC_WIDTH; b++) begin
                    automatic int idx = int'(rd_result_beat) * (AXI_DATA_WIDTH/ACC_WIDTH) + b;
                    if (idx < ARRAY_SIZE)
                        rd_data_mux[b*ACC_WIDTH +: ACC_WIDTH] = rd_data[idx];
                end
            end

            REGION_PERF: begin
                case (rd_beat_addr[3:0])
                    4'h0:    rd_data_mux = {32'b0, perf_total};
                    4'h8:    rd_data_mux = {32'b0, perf_compute};
                    default: rd_data_mux = {32'b0, perf_idle};
                endcase
            end

            default: rd_data_mux = '0;
        endcase
    end

    // Issue SRAM read at start of read transaction for RESULT region
    logic rd_sram_trigger;
    assign rd_row_addr = rd_result_row;
    assign rd_en       = rd_sram_trigger;

    // Read FSM
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_state    <= RD_IDLE;
            rd_addr_reg <= '0;
            rd_id_reg   <= '0;
            rd_len_reg  <= '0;
            rd_beat_cnt <= '0;
            rd_sram_trigger <= 1'b0;
        end else begin
            rd_sram_trigger <= 1'b0;

            case (rd_state)
                RD_IDLE: begin
                    if (s_axi_arvalid) begin
                        rd_addr_reg <= s_axi_araddr;
                        rd_id_reg   <= s_axi_arid;
                        rd_len_reg  <= s_axi_arlen;
                        rd_beat_cnt <= '0;
                        // Trigger SRAM read for result region
                        if (s_axi_araddr[15:12] == REGION_RESULT)
                            rd_sram_trigger <= 1'b1;
                        rd_state <= RD_WAIT;
                    end
                end

                RD_WAIT: begin
                    // 1-cycle wait for SRAM read latency + activation reg
                    rd_state <= RD_DATA;
                end

                RD_DATA: begin
                    if (s_axi_rready) begin
                        if (rd_beat_cnt == rd_len_reg) begin
                            rd_state <= RD_IDLE;
                        end else begin
                            rd_beat_cnt <= rd_beat_cnt + 8'd1;
                            // Trigger next SRAM row if crossing row boundary
                            if (rd_region == REGION_RESULT)
                                rd_sram_trigger <= 1'b1;
                        end
                    end
                end

                default: rd_state <= RD_IDLE;
            endcase
        end
    end

    // Read channel outputs
    assign s_axi_arready = (rd_state == RD_IDLE);
    assign s_axi_rvalid  = (rd_state == RD_DATA);
    assign s_axi_rdata   = rd_data_mux;
    assign s_axi_rresp   = rd_error ? 2'b10 : 2'b00;
    assign s_axi_rlast   = (rd_state == RD_DATA) && (rd_beat_cnt == rd_len_reg);
    assign s_axi_rid     = rd_id_reg;

    // =========================================================================
    // SVA — Assertions (simulation only)
    // =========================================================================
    // synthesis translate_off
    property p_no_start_during_busy;
        @(posedge clk) disable iff (!rst_n)
        tpu_start_r |-> !tpu_busy;
    endproperty
    assert property (p_no_start_during_busy)
        else $error("AXI: start issued while TPU is busy");

    // AXI: AWVALID must remain stable until AWREADY
    property p_aw_stable;
        @(posedge clk) disable iff (!rst_n)
        (s_axi_awvalid && !s_axi_awready) |=> s_axi_awvalid;
    endproperty
    // Note: this is a check on the MASTER, not us. Log as warning.
    // assert property (p_aw_stable) else $warning("AXI master: AWVALID deasserted before AWREADY");

    property p_done_sets_flag;
        @(posedge clk) disable iff (!rst_n)
        tpu_done |=> ctrl_done;
    endproperty
    assert property (p_done_sets_flag)
        else $error("AXI: ctrl_done not set after tpu_done");
    // synthesis translate_on

endmodule
