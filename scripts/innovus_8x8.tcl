# =============================================================================
# Innovus P&R Script - 8x8 Systolic Array MAC Accelerator
# Target: ASAP7 7nm, 667 MHz (1500ps), TT corner
# Adapted from proven 4x4 flow (Feb 15, 2026)
#
# Run from: synthesis/ or PnR/ directory (wherever ../outputs/ has the netlist)
#   innovus -init ../scripts/innovus_8x8.tcl |& tee innovus_8x8_run.rep
# =============================================================================

set VERSION 23  ;# Innovus major version (for API compatibility)

# =============================================================================
# 1. Design Import (MMMC-based)
# =============================================================================
set init_mmmc_file    "../scripts/systolic_top_8x8.mmmc"
set init_verilog      "../outputs/systolic_top_8x8_netlist.v"
set init_top_cell     "systolic_top_ARRAY_SIZE8"
set init_lef_file     [list \
    ../techlef/asap7_tech_4x_201209.lef \
    ../lef/scaled/asap7sc7p5t_28_L_4x_220121a.lef \
    ../lef/scaled/asap7sc7p5t_28_SL_4x_220121a.lef \
]
set init_pwr_net      VDD
set init_gnd_net      VSS

init_design

puts ">>> \[1/12\] Design imported (8x8 systolic array, ARRAY_SIZE=8)."

# =============================================================================
# 2. Design Mode Settings
# =============================================================================
# Check for QRC technology file (required for process <= 32nm extraction)
set QRC_TECH_FILE ""
foreach qrc_candidate [list \
    "../qrc/qrcTechFile" \
    "../qrc/calibre/qrcTechFile" \
    "../asap7PDK/qrc/qrcTechFile" \
] {
    if {[file exists $qrc_candidate]} {
        set QRC_TECH_FILE $qrc_candidate
        puts ">>> Found QRC tech file: $QRC_TECH_FILE"
        break
    }
}

# Set ASAP7 technology node
if {$QRC_TECH_FILE ne ""} {
    if {$VERSION <= 19} {
        setDesignMode -process 7
    } else {
        setDesignMode -process 7 -node N7
    }
    update_rc_corner -name rc_typical -qx_tech_file $QRC_TECH_FILE
    puts ">>> Process set to N7 with QRC extraction."
} else {
    puts ">>> WARNING: No QRC tech file found. Using process=45 workaround."
    puts ">>>   For better accuracy, place qrcTechFile in ../qrc/ and rerun."
    setDesignMode -process 45
}

# Use all available CPUs
setMultiCpuUsage -localCpu 8

# Routing layer constraints: M1 reserved for std cells, route on M2-M7
if {$VERSION <= 20} {
    setNanoRouteMode -routeBottomRoutingLayer 2
    setNanoRouteMode -routeTopRoutingLayer 7
} else {
    setDesignMode -bottomRoutingLayer 2
    setDesignMode -topRoutingLayer 7
}

# Global power net connections
globalNetConnect VDD -type pgpin -pin VDD -inst *
globalNetConnect VSS -type pgpin -pin VSS -inst *

puts ">>> \[2/12\] Design mode configured (M2-M7 routing)."

# =============================================================================
# 3. Floorplan
# =============================================================================
# 8x8 sizing: cell area 70,544 um2, target ~55% utilization
# Core: 358 x 358 um, Die: 370.4 x 370.4 um (6.2um margins)
# Compare 4x4: 180 x 180 core, 192.8 x 192.8 die
floorPlan -site asap7sc7p5t \
    -d 370.42 370.42 6.21 6.21 6.21 6.21

# Snap M1 tracks to cell pins for proper power routing
add_tracks -snap_m1_track_to_cell_pins

puts ">>> \[3/12\] Floorplan created (370.4 x 370.4 um die)."

# =============================================================================
# 4. Pin Placement
# =============================================================================
# 8x8 has 75 inputs, 258 outputs (8x32-bit rd_data + busy + done)
# Die usable height ~358um, so 258 outputs at 1.008um = 260um -> fits
setPinAssignMode -pinEditInBatch true

# Collect input and output pins
set input_pins  [get_db [get_db ports -if {.direction == in}] .name]
set output_pins [get_db [get_db ports -if {.direction == out}] .name]

if {[llength $input_pins] > 0} {
    editPin -fixOverlap 1 -unit MICRON -spreadDirection clockwise \
        -side Left -layer 3 -spreadType center -spacing 2.016 \
        -pin $input_pins
}
if {[llength $output_pins] > 0} {
    editPin -fixOverlap 1 -unit MICRON -spreadDirection clockwise \
        -side Right -layer 3 -spreadType center -spacing 1.008 \
        -pin $output_pins
}

editPin -snap TRACK -pin *
setPinAssignMode -pinEditInBatch false
legalizePin

puts ">>> \[4/12\] Pins placed ([llength $input_pins] in left, [llength $output_pins] out right)."

# =============================================================================
# 5. Power Grid (ASAP7-specific multi-layer mesh)
# =============================================================================

# --- Core rings on M6 (vertical) / M7 (horizontal) ---
setAddRingMode -ring_target default -extend_over_row 0 -ignore_rows 0 \
    -stacked_via_top_layer M7 -stacked_via_bottom_layer M1

addRing -nets {VDD VSS} \
    -type core_rings \
    -layer {top M7 bottom M7 left M6 right M6} \
    -width {top 1.800 bottom 1.800 left 1.800 right 1.800} \
    -spacing {top 0.900 bottom 0.900 left 0.900 right 0.900} \
    -offset {top 0.900 bottom 0.900 left 0.900 right 0.900}

# --- M3/M4 stripes for signal power mesh ---
setAddStripeMode -ignore_block_check false -break_at none \
    -route_over_rows_only false -rows_without_stripes_only false \
    -stacked_via_top_layer M4 -stacked_via_bottom_layer M1

addStripe -nets {VDD VSS} \
    -layer M3 -direction vertical \
    -width 0.072 -spacing 0.936 \
    -set_to_set_distance 12.960 \
    -start_from left -start_offset 6.480

addStripe -nets {VDD VSS} \
    -layer M4 -direction horizontal \
    -width 1.152 -spacing 0.576 \
    -set_to_set_distance 12.960 \
    -start_from bottom -start_offset 6.480

puts ">>> \[5/12\] Power grid created (M3/M4 mesh + M6/M7 rings)."

# =============================================================================
# 6. Special Route (M1 follow-pin power connections)
# =============================================================================
sroute -connect {blockPin padPin padRing corePin floatingStripe} \
    -layerChangeRange {M1 M4} \
    -blockPinTarget {nearestRingStripe nearestTarget} \
    -padPinPortConnect {allPort oneGeom} \
    -checkAlignedSecondaryPin 1 \
    -allowJogging 1 -crossoverViaLayerRange {M1 M4} \
    -allowLayerChange 0 -targetViaLayerRange {M1 M4}

# Pre-route DRC check
verify_drc > innovus_8x8_pre_route_geom.rpt
checkPlace > innovus_8x8_check_place.rep

puts ">>> \[6/12\] Special routing complete. Check innovus_8x8_check_place.rep."

# =============================================================================
# 7. Placement + Timing Optimization
# =============================================================================
# Aggressive opt settings for 0ps-slack design
setOptMode -opt_hold_target_slack    0.02
setOptMode -opt_setup_target_slack   0.02

place_opt_design

# Tie cells
setTieHiLoMode -maxFanout 5
addTieHiLo -prefix TIE -cell {TIELOx1_ASAP7_75t_SL TIEHIx1_ASAP7_75t_SL}

# Verify placement
checkPlace > innovus_8x8_check_place_post.rep

puts ">>> \[7/12\] Placement + opt complete."

# =============================================================================
# 8. Clock Tree Synthesis
# =============================================================================
# Innovus 23.14 place_opt_design uses PODv2 flow -> requires clock_opt_design
if {[catch {clock_opt_design} err]} {
    puts ">>> clock_opt_design failed, trying ccopt_design fallback..."
    ccopt_design
}

# Set propagated clocks for accurate post-CTS timing
set_interactive_constraint_modes [all_constraint_modes -active]
reset_propagated_clock [all_clocks]
set_propagated_clock [all_clocks]

puts ">>> \[8/12\] CTS complete."

# Post-CTS optimization
optDesign -postCTS
optDesign -postCTS -hold

puts ">>> \[9/12\] Post-CTS optimization complete."

# CTS reports
if {[catch {report_ccopt_clock_trees > innovus_8x8_cts_trees.rep}]} {
    catch {report_clock_trees > innovus_8x8_cts_trees.rep}
}
if {[catch {report_ccopt_skew_groups > innovus_8x8_cts_skew.rep}]} {
    catch {report_skew_groups > innovus_8x8_cts_skew.rep}
}

# =============================================================================
# 9. Routing
# =============================================================================
setNanoRouteMode -routeWithSiDriven true
setNanoRouteMode -routeWithTimingDriven true

routeDesign -globalDetail

puts ">>> \[10/12\] Routing complete."

# =============================================================================
# 10. Post-Route Optimization
# =============================================================================
# Fix power vias
editPowerVia -delete_vias 1
editPowerVia -bottom_layer M1 -top_layer M4 -add_vias 1

# Post-route optimization with SI
setAnalysisMode -analysisType onChipVariation -cppr both
optDesign -postRoute
optDesign -postRoute -hold
optDesign -postRoute -si

puts ">>> \[11/12\] Post-route optimization + SI complete."

# =============================================================================
# 11. Filler Cells
# =============================================================================
set fillers_sl {DECAPx10_ASAP7_75t_SL DECAPx6_ASAP7_75t_SL DECAPx4_ASAP7_75t_SL \
                DECAPx2_ASAP7_75t_SL DECAPx1_ASAP7_75t_SL FILLER_ASAP7_75t_SL \
                FILLERxp5_ASAP7_75t_SL}
set fillers_l  {DECAPx10_ASAP7_75t_L DECAPx6_ASAP7_75t_L DECAPx4_ASAP7_75t_L \
                DECAPx2_ASAP7_75t_L DECAPx1_ASAP7_75t_L FILLER_ASAP7_75t_L \
                FILLERxp5_ASAP7_75t_L}
set all_fillers [concat $fillers_sl $fillers_l]
set available_fillers {}
foreach f $all_fillers {
    if {[llength [get_db base_cells $f]] > 0} {
        lappend available_fillers $f
    }
}
if {[llength $available_fillers] > 0} {
    addFiller -cell $available_fillers -prefix FILLER
    ecoRoute -fix_drc
    puts ">>> Fillers inserted: [llength $available_fillers] types."
} else {
    puts ">>> WARNING: No filler cells found in library."
}

puts ">>> \[12/12\] Filler cells inserted."

# =============================================================================
# 12. Final Reports & Outputs
# =============================================================================
# DRC
verify_drc > innovus_8x8_final_geom.rpt

# Timing
report_timing -machine_readable -max_paths 20 -nworst 1 \
    > innovus_8x8_timing_setup.rep
report_timing -machine_readable -max_paths 20 -nworst 1 -late \
    > innovus_8x8_timing_hold.rep

# Area
report_area > innovus_8x8_area.rep

# Power
report_power > innovus_8x8_power.rep

# Summary
summaryReport > innovus_8x8_summary.rep

# Noise (SI)
report_noise -o innovus_8x8_noise.rep

# Output files
defOut -floorplan -netlist -routing ../outputs/systolic_top_8x8_final.def
saveNetlist ../outputs/systolic_top_8x8_final.v
write_sdf ../outputs/systolic_top_8x8_final.sdf
saveDesign ../outputs/systolic_top_8x8_innovus.dat

puts "============================================"
puts " P&R complete: 8x8 Systolic Array"
puts " Clock: 1500ps (667 MHz) / 64 MACs = 42.7 GOPS"
puts ""
puts " DEF:     ../outputs/systolic_top_8x8_final.def"
puts " Netlist: ../outputs/systolic_top_8x8_final.v"
puts " SDF:     ../outputs/systolic_top_8x8_final.sdf"
puts " DB:      ../outputs/systolic_top_8x8_innovus.dat"
puts " Reports: innovus_8x8_*.rep (in run/)"
puts "============================================"
