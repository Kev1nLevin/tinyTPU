# =============================================================================
# Innovus Place & Route Script - 4x4 Systolic Array MAC Accelerator
# Target: ASAP7 7nm PDK (LVT + SLVT, TT corner, 4x scaled)
# Based on: ASU ASAP7 reference flow + custom additions
# Run from: run/ directory
# Command:  cd run && innovus -init ../scripts/innovus.tcl |& tee innovus_run.rep
# =============================================================================

# ---- Innovus version (affects some commands) ----
set VERSION 21

# ---- Paths (relative to run/ directory) ----
set LIB_PATH        "../lib/"
set LEF_PATH        "../lef/scaled/"
set TLEF_PATH       "../techlef/"
set QRC_PATH        "../qrc/"
set OUTPUT_PATH     "../outputs/"

set DESIGN          "systolic_top"

# =============================================================================
# 1. Design Import
# =============================================================================
set init_design_uniquify 1
set init_design_netlisttype {Verilog}
set init_design_settop {1}

set init_verilog    ${OUTPUT_PATH}systolic_top_netlist.v
set init_top_cell   $DESIGN
set init_pwr_net    VDD
set init_gnd_net    VSS

# LEF: tech lef first, then cell lefs
set CELL_LEF "${LEF_PATH}asap7sc7p5t_28_L_4x_220121a.lef ${LEF_PATH}asap7sc7p5t_28_SL_4x_220121a.lef"
set TECH_LEF "${TLEF_PATH}asap7_tech_4x_201209.lef"
set init_lef_file "$TECH_LEF $CELL_LEF"

set fp_core_cntl {aspect}
set fp_aspect_ratio {1.0000}
set extract_shrink_factor {1.0}
set init_assign_buffer {0}

# Timing: use MMMC for proper analysis view setup
set init_cpf_file  {}
set init_mmmc_file {../scripts/systolic_top.mmmc}

init_design
puts ">>> \[1/12\] Design imported."

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
# NOTE: process <= 32nm requires QRC tech file for RC extraction.
# If QRC is available, set N7; otherwise use process 45 as workaround.
if {$QRC_TECH_FILE ne ""} {
    if {$VERSION <= 19} {
        setDesignMode -process 7
    } else {
        setDesignMode -process 7 -node N7
    }
    # Update RC corner with QRC file
    update_rc_corner -name rc_typical -qx_tech_file $QRC_TECH_FILE
    puts ">>> Process set to N7 with QRC extraction."
} else {
    puts ">>> WARNING: No QRC tech file found. Using process=45 workaround."
    puts ">>>   For better accuracy, place qrcTechFile in ../qrc/ and rerun."
    puts ">>>   Download from ASAP7 PDK: https://github.com/The-OpenROAD-Project/asap7"
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
# ASAP7 4x scaled cell dimensions
set cellheight [expr 0.270 * 4]   ;# = 1.080 um (4x scaled)
set cellhgrid  0.216

# Power ring dimensions (ASAP7-specific, must be on-grid)
set FP_RING_OFFSET 0.384
set FP_RING_WIDTH  2.176
set FP_RING_SPACE  0.384
set FP_RING_SIZE   [expr {$FP_RING_SPACE + 2*$FP_RING_WIDTH + $FP_RING_OFFSET + 1.1}]

# Floorplan sizing
# FP_TARGET = number of standard cell rows (controls die size)
# FP_MUL = 5 gives square aspect ratio
# Calculated: cell_area=17406um2, at 60% util need ~29000um2 core
# FP_TARGET=167 gives 180x180um = 32530um2 (~53% util, good for routability)
# TODO: adjust FP_TARGET if utilization is too low/high in reports
set FP_TARGET 167
set FP_MUL   5

set fpxdim [expr $cellhgrid * $FP_TARGET * $FP_MUL]
set fpydim [expr $cellheight * $FP_TARGET]

fpiGetSnapRule

floorPlan -site asap7sc7p5t -s $fpxdim $fpydim $FP_RING_SIZE $FP_RING_SIZE $FP_RING_SIZE $FP_RING_SIZE -noSnap

# Well taps (required for latchup prevention)
addWellTap -cell TAPCELL_ASAP7_75t_L -cellInterval 12.960 -inRowOffset 1.296

# Track alignment (Innovus 21+)
if {$VERSION >= 21} {
    add_tracks -snap_m1_track_to_cell_pins
    add_tracks -mode replace -offsets {M5 vertical 0}
    deleteAllFPObjects
    addWellTap -cell TAPCELL_ASAP7_75t_L -cellInterval 12.960 -inRowOffset 1.296
}

puts ">>> \[3/12\] Floorplan created (${fpxdim}um x ${fpydim}um)."

# =============================================================================
# 4. Pin Placement
# =============================================================================
# Place pins on M3: inputs on left, outputs on right
# NOTE: 130 output pins need ~131um at 1.008um spacing (die usable height ~170um)
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

puts ">>> \[4/12\] Pins placed (inputs left, outputs right)."

# =============================================================================
# 5. Power Grid (ASAP7-specific multi-layer mesh)
# =============================================================================

# --- Core rings on M6 (vertical) / M7 (horizontal) ---
setAddRingMode -ring_target default -extend_over_row 0 -ignore_rows 0 \
    -avoid_short 0 -skip_crossing_trunks none \
    -stacked_via_top_layer Pad -stacked_via_bottom_layer M1 \
    -via_using_exact_crossover_size 1 -orthogonal_only true \
    -skip_via_on_pin {standardcell} -skip_via_on_wire_shape {noshape}

addRing -nets {VDD VSS} -type core_rings -follow core \
    -layer {top M7 bottom M7 left M6 right M6} \
    -width $FP_RING_WIDTH -spacing $FP_RING_SPACE \
    -offset $FP_RING_OFFSET -center 0 -threshold 0 \
    -jog_distance 0 -snap_wire_center_to_grid None

# --- M2 horizontal follow rails (one per std cell row) ---
# VDD rails
addStripe -skip_via_on_wire_shape blockring \
    -direction horizontal \
    -set_to_set_distance [expr 2*$cellheight] \
    -skip_via_on_pin Standardcell \
    -stacked_via_top_layer  M1 \
    -layer M2 \
    -width 0.072 \
    -nets {VDD} \
    -stacked_via_bottom_layer M1 \
    -start_from bottom \
    -snap_wire_center_to_grid None \
    -start_offset -0.044 \
    -stop_offset -0.044

# VSS rails
addStripe -skip_via_on_wire_shape blockring \
    -direction horizontal \
    -set_to_set_distance [expr 2*$cellheight] \
    -skip_via_on_pin Standardcell \
    -stacked_via_top_layer  M1 \
    -layer M2 \
    -width 0.072 \
    -nets {VSS} \
    -stacked_via_bottom_layer M1 \
    -start_from bottom \
    -snap_wire_center_to_grid None \
    -start_offset [expr $cellheight - 0.044] \
    -stop_offset -0.044

# --- M3 vertical power stripes ---
set m3pwrwidth       0.936
set m3pwrspacing     0.360
set m3pwrset2setdist 12.960

addStripe -skip_via_on_wire_shape Noshape \
    -set_to_set_distance $m3pwrset2setdist \
    -skip_via_on_pin Standardcell \
    -stacked_via_top_layer Pad \
    -spacing $m3pwrspacing \
    -xleft_offset 0.360 \
    -layer M3 \
    -width $m3pwrwidth \
    -nets {VDD VSS} \
    -stacked_via_bottom_layer M2 \
    -start_from left

# Fix power vias for Innovus 17
if {$VERSION == 17} {
    editPowerVia -delete_vias 1 -top_layer 4 -bottom_layer 3
    editPowerVia -add_vias 1
}

# --- M4 horizontal power stripes ---
set m4pwrwidth       0.864
set m4pwrspacing     0.864
set m4pwrset2setdist 21.6

addStripe -skip_via_on_wire_shape Noshape \
    -direction horizontal \
    -set_to_set_distance $m4pwrset2setdist \
    -skip_via_on_pin Standardcell \
    -stacked_via_top_layer M7 \
    -spacing $m4pwrspacing \
    -layer M4 \
    -width $m4pwrwidth \
    -nets {VDD VSS} \
    -stacked_via_bottom_layer M3 \
    -start_from bottom

# --- Special route: connect std cell pins to power mesh ---
setSrouteMode -reset
setSrouteMode -viaConnectToShape {noshape}
sroute -connect {corePin} \
    -layerChangeRange {M1(1) M7(1)} \
    -blockPinTarget {nearestTarget} \
    -floatingStripeTarget {blockring padring ring stripe ringpin blockpin followpin} \
    -deleteExistingRoutes \
    -allowJogging 0 \
    -crossoverViaLayerRange {M1(1) Pad(10)} \
    -nets {VDD VSS} \
    -allowLayerChange 0 \
    -targetViaLayerRange {M1(1) Pad(10)}

editPowerVia -add_vias 1 -orthogonal_only 0

# DRC check on power grid
verify_drc

# Colorize power mesh for double-patterning
colorizePowerMesh

puts ">>> \[5/12\] Power grid created (M2 rails + M3/M4 stripes + M6/M7 rings)."

# =============================================================================
# 6. Placement + Pre-CTS Optimization
# =============================================================================
setOptMode -holdTargetSlack  0.020
setOptMode -setupTargetSlack 0.020

place_opt_design

# Add tie-hi/lo cells for floating gates
setTieHiLoMode -maxFanout 5
addTieHiLo -prefix TIE -cell {TIELOx1_ASAP7_75t_SL TIEHIx1_ASAP7_75t_SL}

puts ">>> \[6/12\] Placement + optimization complete."

# Check placement
checkPlace > innovus_check_place.rep

# =============================================================================
# 7. Clock Tree Synthesis
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

puts ">>> \[7/12\] CTS complete."

# Post-CTS optimization
optDesign -postCTS
optDesign -postCTS -hold

puts ">>> \[8/12\] Post-CTS optimization complete."

# CTS reports
if {[catch {report_ccopt_clock_trees > innovus_cts_trees.rep}]} {
    catch {report_clock_trees > innovus_cts_trees.rep}
}
if {[catch {report_ccopt_skew_groups > innovus_cts_skew.rep}]} {
    catch {report_skew_groups > innovus_cts_skew.rep}
}

# =============================================================================
# 8. Routing
# =============================================================================
legalizePin

routeDesign

puts ">>> \[9/12\] Routing complete."

# =============================================================================
# 9. Post-Route Optimization + SI Analysis
# =============================================================================
# Fix power via coloring issues from routing
editPowerVia -delete_vias 1 -top_layer 7 -bottom_layer 6
editPowerVia -delete_vias 1 -top_layer 6 -bottom_layer 5
editPowerVia -delete_vias 1 -top_layer 5 -bottom_layer 4
editPowerVia -delete_vias 1 -top_layer 4 -bottom_layer 3
editPowerVia -delete_vias 1 -top_layer 3 -bottom_layer 2
editPowerVia -delete_vias 1 -top_layer 2 -bottom_layer 1
editPowerVia -add_vias 1

# Enable on-chip variation and SI analysis
setAnalysisMode -analysisType onChipVariation
setSIMode -enable_glitch_report true
setSIMode -enable_glitch_propagation true
setSIMode -enable_delay_report true

# Post-route optimization (setup then hold)
optDesign -postRoute
optDesign -postRoute -hold

puts ">>> \[10/12\] Post-route optimization + SI analysis complete."

# Noise reports
report_noise -threshold 0.2 > innovus_noise.rep
report_noise -bumpy_waveform > innovus_noise_bumpy.rep

# =============================================================================
# 10. Filler Cells
# =============================================================================
# Try adding fillers - cell names vary by PDK version
if {[catch {
    addFiller -cell {FILLER_ASAP7_75t_L FILLERxp5_ASAP7_75t_L FILLER_ASAP7_75t_SL FILLERxp5_ASAP7_75t_SL} -prefix FILLER
} err]} {
    puts ">>> WARNING: Filler insertion failed: $err"
    puts ">>>   This is common - fillers may be in LEF but not .lib"
}

puts ">>> \[11/12\] Fillers inserted."

# =============================================================================
# 11. Verification
# =============================================================================
verify_drc                          > innovus_verify_drc.rep
verifyConnectivity -type all        > innovus_verify_conn.rep
verifyProcessAntenna                > innovus_verify_antenna.rep

puts ">>> \[12/12\] Verification complete."

# =============================================================================
# 12. Final Reports
# =============================================================================
report_timing -max_paths 10 -late   > innovus_timing_setup.rep
report_timing -max_paths 10 -early  > innovus_timing_hold.rep
report_area                         > innovus_area.rep
report_power                        > innovus_power.rep
summaryReport                       > innovus_summary.rep

# =============================================================================
# 13. Export Outputs
# =============================================================================

# DEF
set defOutLefVia 1
set defOutLefNDR 1
defOut -netlist -routing -allLayers ${OUTPUT_PATH}${DESIGN}_final.def

# Post-route netlist
saveNetlist ${OUTPUT_PATH}${DESIGN}_final.v

# Post-route SDF
write_sdf ${OUTPUT_PATH}${DESIGN}_final.sdf

# GDS export
# TODO: uncomment and update paths to merge GDS cell libraries if available
# streamOut ${OUTPUT_PATH}${DESIGN}.gds \
#     -mapFile {../gds/gds2.map} \
#     -libName DesignLib \
#     -uniquifyCellNames \
#     -outputMacros \
#     -stripes 1 \
#     -mode ALL \
#     -units 4000 \
#     -merge { ../gds/asap7sc7p5t_28_L_220121a_scaled4x.gds ../gds/asap7sc7p5t_28_SL_220121a_scaled4x.gds }

# Save Innovus database (reopen with: restoreDesign <path>)
saveDesign ${OUTPUT_PATH}${DESIGN}_innovus.dat

puts ""
puts "============================================"
puts " P&R Complete: $DESIGN"
puts "============================================"
puts " Check these reports:"
puts "   innovus_timing_setup.rep  -> slack must be >= 0"
puts "   innovus_timing_hold.rep   -> slack must be >= 0"
puts "   innovus_verify_drc.rep    -> target: 0 violations"
puts "   innovus_verify_conn.rep   -> target: 0 violations"
puts "   innovus_summary.rep       -> PPA overview"
puts ""
puts " Outputs in ${OUTPUT_PATH}:"
puts "   ${DESIGN}_final.def       (DEF layout)"
puts "   ${DESIGN}_final.v         (post-route netlist)"
puts "   ${DESIGN}_final.sdf       (post-route timing)"
puts "   ${DESIGN}_innovus.dat     (Innovus database)"
puts "============================================"
