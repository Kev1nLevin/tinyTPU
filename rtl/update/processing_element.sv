// =============================================================================
// Module: processing_element
// Description: Systolic Array Processing Element (PE) — Production
//              Wraps a MAC unit and adds systolic data flow registers.
//              - Weight (a) flows top-to-bottom (vertical)
//              - Activation (b) flows left-to-right (horizontal)
//              Output-stationary dataflow.
// =============================================================================

module processing_element #(
    parameter DATA_WIDTH = 16,
    parameter ACC_WIDTH  = 32
)(
    input  logic                         clk,
    input  logic                         rst_n,
    input  logic                         en,
    input  logic                         clear_acc,

    input  logic signed [DATA_WIDTH-1:0] a_in,
    input  logic signed [DATA_WIDTH-1:0] b_in,

    output logic signed [DATA_WIDTH-1:0] a_out,
    output logic signed [DATA_WIDTH-1:0] b_out,

    output logic signed [ACC_WIDTH-1:0]  result_out
);

    // Systolic pass-through: 1-cycle delay
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            a_out <= '0;
            b_out <= '0;
        end else if (en) begin
            a_out <= a_in;
            b_out <= b_in;
        end
    end

    mac_unit #(
        .DATA_WIDTH (DATA_WIDTH),
        .ACC_WIDTH  (ACC_WIDTH)
    ) u_mac (
        .clk       (clk),
        .rst_n     (rst_n),
        .en        (en),
        .clear_acc (clear_acc),
        .a_in      (a_in),
        .b_in      (b_in),
        .acc_out   (result_out)
    );

    // =========================================================================
    // SVA — pass-through delay check
    // =========================================================================
    // synthesis translate_off
    property p_a_delay;
        @(posedge clk) disable iff (!rst_n)
        en |=> (a_out == $past(a_in));
    endproperty
    assert property (p_a_delay)
        else $error("PE: a_out not delayed by 1 cycle");

    property p_b_delay;
        @(posedge clk) disable iff (!rst_n)
        en |=> (b_out == $past(b_in));
    endproperty
    assert property (p_b_delay)
        else $error("PE: b_out not delayed by 1 cycle");
    // synthesis translate_on

endmodule
