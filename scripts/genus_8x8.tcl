# =============================================================================
# Genus Synthesis Script - 8x8 Systolic Array MAC Accelerator
# Target: ASAP7 7nm, 667 MHz (1500ps), TT corner
# Run from: run/ directory
# Command:  cd run && genus -f ../scripts/genus_8x8.tcl |& tee genus_8x8_run.rep
# =============================================================================

# Paths relative to run/ directory
set RTL_PATH        "../rtl/"
set LIB_PATH        "../lib/"
set LEF_PATH        "../lef/scaled/"
set TLEF_PATH       "../techlef/"
set QRC_PATH        "../qrc/"

set DESIGN          "systolic_top"
set ARRAY_SIZE      8

# ---- Library Setup (LVT + SLVT, TT corner) ----
# ASAP7 .lib uses picoseconds as time unit
set LIB_LIST { asap7sc7p5t_AO_LVT_TT_nldm_211120.lib   asap7sc7p5t_INVBUF_LVT_TT_nldm_220122.lib   asap7sc7p5t_OA_LVT_TT_nldm_211120.lib   asap7sc7p5t_SEQ_LVT_TT_nldm_220123.lib   asap7sc7p5t_SIMPLE_LVT_TT_nldm_211120.lib \
              asap7sc7p5t_AO_SLVT_TT_nldm_211120.lib  asap7sc7p5t_INVBUF_SLVT_TT_nldm_220122.lib  asap7sc7p5t_OA_SLVT_TT_nldm_211120.lib  asap7sc7p5t_SEQ_SLVT_TT_nldm_220123.lib  asap7sc7p5t_SIMPLE_SLVT_TT_nldm_211120.lib }

set LEF_LIST { asap7_tech_4x_201209.lef asap7sc7p5t_28_L_4x_220121a.lef asap7sc7p5t_28_SL_4x_220121a.lef }

# All RTL files (SystemVerilog)
set RTL_LIST { mac_unit.sv processing_element.sv systolic_array_4x4.sv input_skew_controller.sv systolic_controller.sv systolic_top.sv }

# ---- Tool Setup ----
set_db init_lib_search_path "$LIB_PATH $LEF_PATH $TLEF_PATH"
set_db init_hdl_search_path $RTL_PATH
set_db / .library "$LIB_LIST"
set_db lef_library "$LEF_LIST"

# ---- Read RTL ----
read_hdl -sv ${RTL_LIST}

# ---- Elaborate with 8x8 parameter override ----
elaborate $DESIGN -parameters {{ARRAY_SIZE 8}}

puts "============================================"
puts " Elaborated $DESIGN with ARRAY_SIZE = $ARRAY_SIZE"
puts " Expected: 64 PEs, ~4200 flip-flops"
puts "============================================"

# ---- Constraints ----
# 1500ps = 667 MHz — same target as the 4x4 P&R that achieved timing closure
# Critical path is within a single PE (MAC accumulator carry chain)
# so it should not change much with array size scaling.
# The extra routing for 64 PEs vs 16 may eat into slack during P&R.
set CLK_PERIOD 1500  ;# picoseconds (1500ps = 667 MHz)

create_clock -name "clk" -period $CLK_PERIOD [get_ports clk]
set_input_delay  -clock clk [expr $CLK_PERIOD * 0.3] [all_inputs]
set_output_delay -clock clk [expr $CLK_PERIOD * 0.3] [all_outputs]

# Remove clock port from input delay constraint
remove_input_delay [get_ports clk]

# Async reset - don't time this path
set_false_path -from [get_ports rst_n]

# ---- Synthesis ----
syn_generic
syn_map
syn_opt

# ---- Export Netlist ----
write_hdl > ../outputs/systolic_top_8x8_netlist.v
write_sdc > ../outputs/systolic_top_8x8.sdc
write_sdf > ../outputs/systolic_top_8x8.sdf

# ---- Reports ----
report timing                 > genus_8x8_timing.rep
report timing -max_paths 10   > genus_8x8_timing_top10.rep
report area                   > genus_8x8_area.rep
report gates                  > genus_8x8_cell.rep
report power                  > genus_8x8_power.rep
report qor                    > genus_8x8_qor.rep
report summary                > genus_8x8_summary.rep
report hierarchy              > genus_8x8_hierarchy.rep
report datapath               > genus_8x8_datapath.rep

puts "============================================"
puts " Synthesis complete: $DESIGN (${ARRAY_SIZE}x${ARRAY_SIZE})"
puts " Clock period: ${CLK_PERIOD}ps (667 MHz)"
puts " Netlist: ../outputs/systolic_top_8x8_netlist.v"
puts " SDC:     ../outputs/systolic_top_8x8.sdc"
puts " SDF:     ../outputs/systolic_top_8x8.sdf"
puts " Reports: genus_8x8_*.rep (in run/)"
puts "============================================"

# Keep Genus open for interactive exploration
# Type 'exit' to quit
