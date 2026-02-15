# =============================================================================
# Genus Synthesis Script - 4x4 Systolic Array MAC Accelerator
# Reference: ASAP7 PDK flow (LVT + SLVT, TT corner, picosecond units)
# =============================================================================

# TODO change these paths to match your directory structure
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
# So all timing values here are in picoseconds:
#   600ps  = 1.67 GHz (very aggressive)
#   1000ps = 1.0  GHz (moderate)
#   1500ps = 667  MHz (relaxed)
# Start with 1000ps. If timing fails, relax to 1500ps.

set CLK_PERIOD 1000  ;# picoseconds

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
# TODO this will overwrite any previous netlist. Comment out if you don't want this
write_hdl > ../outputs/systolic_top_netlist.v

# Write SDC for Innovus P&R
write_sdc > ../outputs/systolic_top.sdc

# Write SDF for gate-level simulation
write_sdf > ../outputs/systolic_top.sdf

# ---- Reports ----
report timing                 > ./genus_timing.rep
report area                   > ./genus_area.rep
report gates                  > ./genus_cell.rep
report power                  > ./genus_power.rep
report transistor_count       > ./genus_transistor_count.rep
report transistor_count -hier > ./genus_transistor_count_hier.rep

puts "============================================"
puts " Synthesis complete: $DESIGN"
puts " Clock period: ${CLK_PERIOD}ps"
puts " Netlist: ../outputs/systolic_top_netlist.v"
puts " Check genus_timing.rep for slack"
puts "============================================"
