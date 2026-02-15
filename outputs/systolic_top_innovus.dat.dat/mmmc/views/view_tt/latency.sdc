set_clock_latency -source -early -max -rise  -50.4453 [get_ports {clk}] -clock clk 
set_clock_latency -source -early -max -fall  -50.0261 [get_ports {clk}] -clock clk 
set_clock_latency -source -late -max -rise  -50.4453 [get_ports {clk}] -clock clk 
set_clock_latency -source -late -max -fall  -50.0261 [get_ports {clk}] -clock clk 
