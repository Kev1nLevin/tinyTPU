// =============================================================================
// Module: sram_sp
// Description: Behavioral single-port SRAM wrapper.
//              Swap this module with a foundry SRAM macro or OpenRAM instance
//              for physical implementation. Synthesis tools will infer block
//              RAM from this pattern for FPGA targets.
//
//              Interface: synchronous read, synchronous write, single port.
//              Read data appears one cycle after address is presented.
// =============================================================================

module sram_sp #(
    parameter DEPTH     = 32,
    parameter WIDTH     = 512,
    parameter ADDR_BITS = $clog2(DEPTH)
)(
    input  logic                 clk,
    input  logic                 ce,      // chip enable
    input  logic                 we,      // write enable (ce & we = write)
    input  logic [ADDR_BITS-1:0] addr,
    input  logic [WIDTH-1:0]     din,
    output logic [WIDTH-1:0]     dout
);

    // Synthesis hint for FPGA block RAM inference
    (* ram_style = "block" *)
    logic [WIDTH-1:0] mem [DEPTH];

    always_ff @(posedge clk) begin
        if (ce) begin
            if (we)
                mem[addr] <= din;
            dout <= mem[addr];
        end
    end

    // ==== Simulation-only initialization ====
    // synthesis translate_off
    initial begin
        for (int i = 0; i < DEPTH; i++)
            mem[i] = '0;
    end
    // synthesis translate_on

endmodule
