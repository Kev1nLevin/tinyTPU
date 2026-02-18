// =============================================================================
// Module: tpu_top
// Description: Top-Level TPU Module (Production)
//              Integrates AXI4 wrapper around systolic datapath.
//              Designed for ASAP7 7nm target, integration with RV64 CPU.
//
//              Production enhancements:
//              - Synchronous reset release (2-stage synchronizer)
//              - Clean port naming
//              - Parameterized for different array sizes
//
//              Features:
//              - 32×32 output-stationary systolic array (1024 PEs)
//              - BF16 inputs, FP32 accumulation
//              - Double-buffered input SRAMs
//              - Registered activation unit (NONE/ReLU/GeLU)
//              - Per-column FP32 bias addition
//              - Accumulate mode for K-dimension tiling
//              - Performance counters (total/compute/idle cycles)
//              - AXI4 MMIO slave with WSTRB, SLVERR, busy protection
//              - Level-sensitive interrupt
//
//              Integration: connect to RV64 CPU AXI master port
// =============================================================================

module tpu_top #(
    parameter AXI_DATA_WIDTH = 64,
    parameter AXI_ADDR_WIDTH = 20,
    parameter AXI_ID_WIDTH   = 4,
    parameter ARRAY_SIZE     = 32,
    parameter DATA_WIDTH     = 16,
    parameter ACC_WIDTH      = 32
)(
    input  logic                          clk,
    input  logic                          rst_n,     // asynchronous active-low reset

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

    // Interrupt output (active high, level sensitive)
    output logic                          irq
);

    // =========================================================================
    // Reset Synchronizer — synchronous release of asynchronous reset
    // Prevents metastability on reset deassertion.
    // =========================================================================
    logic rst_n_sync;
    logic [1:0] rst_pipe;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rst_pipe <= 2'b00;
        else
            rst_pipe <= {rst_pipe[0], 1'b1};
    end
    assign rst_n_sync = rst_pipe[1];

    // =========================================================================
    // AXI4 Wrapper (bridges AXI bus to systolic datapath)
    // =========================================================================
    tpu_axi4_wrapper #(
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .ARRAY_SIZE     (ARRAY_SIZE),
        .DATA_WIDTH     (DATA_WIDTH),
        .ACC_WIDTH      (ACC_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH)
    ) u_axi_wrapper (
        .clk            (clk),
        .rst_n          (rst_n_sync),

        .s_axi_awid     (s_axi_awid),
        .s_axi_awaddr   (s_axi_awaddr),
        .s_axi_awlen    (s_axi_awlen),
        .s_axi_awsize   (s_axi_awsize),
        .s_axi_awburst  (s_axi_awburst),
        .s_axi_awvalid  (s_axi_awvalid),
        .s_axi_awready  (s_axi_awready),

        .s_axi_wdata    (s_axi_wdata),
        .s_axi_wstrb    (s_axi_wstrb),
        .s_axi_wlast    (s_axi_wlast),
        .s_axi_wvalid   (s_axi_wvalid),
        .s_axi_wready   (s_axi_wready),

        .s_axi_bid      (s_axi_bid),
        .s_axi_bresp    (s_axi_bresp),
        .s_axi_bvalid   (s_axi_bvalid),
        .s_axi_bready   (s_axi_bready),

        .s_axi_arid     (s_axi_arid),
        .s_axi_araddr   (s_axi_araddr),
        .s_axi_arlen    (s_axi_arlen),
        .s_axi_arsize   (s_axi_arsize),
        .s_axi_arburst  (s_axi_arburst),
        .s_axi_arvalid  (s_axi_arvalid),
        .s_axi_arready  (s_axi_arready),

        .s_axi_rid      (s_axi_rid),
        .s_axi_rdata    (s_axi_rdata),
        .s_axi_rresp    (s_axi_rresp),
        .s_axi_rlast    (s_axi_rlast),
        .s_axi_rvalid   (s_axi_rvalid),
        .s_axi_rready   (s_axi_rready),

        .irq            (irq)
    );

endmodule
