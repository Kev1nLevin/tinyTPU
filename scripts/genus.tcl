# =============================================================================
# Genus Synthesis Script - 4x4 Systolic Array MAC Accelerator
# Run from: run/ directory
# Command:  cd run && genus -f ../scripts/genus.tcl |& tee genus_run.rep
# =============================================================================

# All paths are relative to the run/ directory
set RTL_PATH        "../sources/"
set LIB_PATH        "../lib/"
set LEF_PATH        "../lef/scaled/"
set TLEF_PATH       "../techlef/"
set QRC_PATH        "../qrc/"

# TODO change design name if you rename the top module
set DESIGN          "systolic_top"

# ---- Library Setup (LVT + SLVT, TT corner) ----
# NOTE: ASAP7 .lib uses picoseconds as time unit
# Clock period and all delays below are in picoseconds

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

# ---- Elaborate ----
elaborate $DESIGN

# ---- Constraints ----
# IMPORTANT: ASAP7 .lib files use picoseconds as the time unit
#   600ps  = 1.67 GHz (very aggressive)
#   1000ps = 1.0  GHz (moderate)
#   1500ps = 667  MHz (relaxed)

# Previous runs: 1000ps (0ps slack), 1200ps (1ps slack) — too tight for P&R
# 1500ps gives ~300ps margin for routing parasitics and CTS insertion
set CLK_PERIOD 1500  ;# picoseconds (1500ps = 667 MHz, safe for P&R closure)
# set CLK_PERIOD 1200  ;# picoseconds (1200ps = 833 MHz)
# set CLK_PERIOD 1000  ;# picoseconds (1000ps = 1 GHz, aggressive)

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
write_hdl > ../outputs/systolic_top_netlist.v
write_sdc > ../outputs/systolic_top.sdc
write_sdf > ../outputs/systolic_top.sdf

# ---- Reports (all land in run/ directory) ----
report timing                 > genus_timing.rep
report area                   > genus_area.rep
report gates                  > genus_cell.rep
report power                  > genus_power.rep
report qor                    > genus_qor.rep
report summary                > genus_summary.rep
report hierarchy              > genus_hierarchy.rep
report datapath               > genus_datapath.rep

puts "============================================"
puts " Synthesis complete: $DESIGN"
puts " Clock period: ${CLK_PERIOD}ps"
puts " Netlist: ../outputs/systolic_top_netlist.v"
puts " SDC:     ../outputs/systolic_top.sdc"
puts " SDF:     ../outputs/systolic_top.sdf"
puts " Reports: genus_*.rep (in run/)"
puts "============================================"

# Keep Genus open for interactive exploration
# Type 'exit' to quit or explore with:
#   report timing -max_paths 10
#   report timing -from [all_registers] -to [all_registers] -max_paths 5
#   gui_show   (to open schematic viewer)
