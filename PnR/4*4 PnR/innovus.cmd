#######################################################
#                                                     
#  Innovus Command Logging File                     
#  Created on Sun Feb 15 05:57:53 2026                
#                                                     
#######################################################

#@(#)CDS: Innovus v23.14-s088_1 (64bit) 02/28/2025 12:25 (Linux 3.10.0-693.el7.x86_64)
#@(#)CDS: NanoRoute 23.14-s088_1 NR250219-0822/23_14-UB (database version 18.20.661) {superthreading v2.20}
#@(#)CDS: AAE 23.14-s018 (64bit) 02/28/2025 (Linux 3.10.0-693.el7.x86_64)
#@(#)CDS: CTE 23.14-s036_1 () Feb 22 2025 01:17:26 ( )
#@(#)CDS: SYNTECH 23.14-s010_1 () Feb 19 2025 23:56:49 ( )
#@(#)CDS: CPE v23.14-s082
#@(#)CDS: IQuantus/TQuantus 23.1.1-s336 (64bit) Mon Jan 20 22:11:00 PST 2025 (Linux 3.10.0-693.el7.x86_64)

set_global _enable_mmmc_by_default_flow      $CTE::mmmc_default
suppressMessage ENCEXT-2799
getVersion
set init_design_uniquify 1
set init_design_netlisttype Verilog
set init_design_settop 1
set init_verilog ../outputs/systolic_top_netlist.v
set init_top_cell systolic_top
set init_pwr_net VDD
set init_gnd_net VSS
set init_lef_file {../techlef/asap7_tech_4x_201209.lef ../lef/scaled/asap7sc7p5t_28_L_4x_220121a.lef ../lef/scaled/asap7sc7p5t_28_SL_4x_220121a.lef}
set fp_core_cntl aspect
set fp_aspect_ratio 1.0000
set extract_shrink_factor 1.0
set init_assign_buffer 0
set init_cpf_file {}
set init_mmmc_file ../scripts/systolic_top.mmmc
init_design
setDesignMode -process 45
setMultiCpuUsage -localCpu 8
setDesignMode -bottomRoutingLayer 2
setDesignMode -topRoutingLayer 7
globalNetConnect VDD -type pgpin -pin VDD -inst *
globalNetConnect VSS -type pgpin -pin VSS -inst *
floorPlan -site asap7sc7p5t -s 180.36 180.36 6.22 6.22 6.22 6.22 -noSnap
addWellTap -cell TAPCELL_ASAP7_75t_L -cellInterval 12.960 -inRowOffset 1.296
add_tracks -snap_m1_track_to_cell_pins
add_tracks -mode replace -offsets {M5 vertical 0}
deleteAllFPObjects
addWellTap -cell TAPCELL_ASAP7_75t_L -cellInterval 12.960 -inRowOffset 1.296
setPinAssignMode -pinEditInBatch true
editPin -fixOverlap 1 -unit MICRON -spreadDirection clockwise -side Left -layer 3 -spreadType center -spacing 2.016 -pin {clk rst_n wr_en_a wr_en_b wr_row_addr[1] wr_row_addr[0] wr_data[3][7] wr_data[3][6] wr_data[3][5] wr_data[3][4] wr_data[3][3] wr_data[3][2] wr_data[3][1] wr_data[3][0] wr_data[2][7] wr_data[2][6] wr_data[2][5] wr_data[2][4] wr_data[2][3] wr_data[2][2] wr_data[2][1] wr_data[2][0] wr_data[1][7] wr_data[1][6] wr_data[1][5] wr_data[1][4] wr_data[1][3] wr_data[1][2] wr_data[1][1] wr_data[1][0] wr_data[0][7] wr_data[0][6] wr_data[0][5] wr_data[0][4] wr_data[0][3] wr_data[0][2] wr_data[0][1] wr_data[0][0] start rd_row_addr[1] rd_row_addr[0]}
editPin -fixOverlap 1 -unit MICRON -spreadDirection clockwise -side Right -layer 3 -spreadType center -spacing 1.008 -pin {busy done rd_data[3][31] rd_data[3][30] rd_data[3][29] rd_data[3][28] rd_data[3][27] rd_data[3][26] rd_data[3][25] rd_data[3][24] rd_data[3][23] rd_data[3][22] rd_data[3][21] rd_data[3][20] rd_data[3][19] rd_data[3][18] rd_data[3][17] rd_data[3][16] rd_data[3][15] rd_data[3][14] rd_data[3][13] rd_data[3][12] rd_data[3][11] rd_data[3][10] rd_data[3][9] rd_data[3][8] rd_data[3][7] rd_data[3][6] rd_data[3][5] rd_data[3][4] rd_data[3][3] rd_data[3][2] rd_data[3][1] rd_data[3][0] rd_data[2][31] rd_data[2][30] rd_data[2][29] rd_data[2][28] rd_data[2][27] rd_data[2][26] rd_data[2][25] rd_data[2][24] rd_data[2][23] rd_data[2][22] rd_data[2][21] rd_data[2][20] rd_data[2][19] rd_data[2][18] rd_data[2][17] rd_data[2][16] rd_data[2][15] rd_data[2][14] rd_data[2][13] rd_data[2][12] rd_data[2][11] rd_data[2][10] rd_data[2][9] rd_data[2][8] rd_data[2][7] rd_data[2][6] rd_data[2][5] rd_data[2][4] rd_data[2][3] rd_data[2][2] rd_data[2][1] rd_data[2][0] rd_data[1][31] rd_data[1][30] rd_data[1][29] rd_data[1][28] rd_data[1][27] rd_data[1][26] rd_data[1][25] rd_data[1][24] rd_data[1][23] rd_data[1][22] rd_data[1][21] rd_data[1][20] rd_data[1][19] rd_data[1][18] rd_data[1][17] rd_data[1][16] rd_data[1][15] rd_data[1][14] rd_data[1][13] rd_data[1][12] rd_data[1][11] rd_data[1][10] rd_data[1][9] rd_data[1][8] rd_data[1][7] rd_data[1][6] rd_data[1][5] rd_data[1][4] rd_data[1][3] rd_data[1][2] rd_data[1][1] rd_data[1][0] rd_data[0][31] rd_data[0][30] rd_data[0][29] rd_data[0][28] rd_data[0][27] rd_data[0][26] rd_data[0][25] rd_data[0][24] rd_data[0][23] rd_data[0][22] rd_data[0][21] rd_data[0][20] rd_data[0][19] rd_data[0][18] rd_data[0][17] rd_data[0][16] rd_data[0][15] rd_data[0][14] rd_data[0][13] rd_data[0][12] rd_data[0][11] rd_data[0][10] rd_data[0][9] rd_data[0][8] rd_data[0][7] rd_data[0][6] rd_data[0][5] rd_data[0][4] rd_data[0][3] rd_data[0][2] rd_data[0][1] rd_data[0][0]}
editPin -snap TRACK -pin *
setPinAssignMode -pinEditInBatch false
legalizePin
setAddRingMode -ring_target default -extend_over_row 0 -ignore_rows 0 -avoid_short 0 -skip_crossing_trunks none -stacked_via_top_layer Pad -stacked_via_bottom_layer M1 -via_using_exact_crossover_size 1 -orthogonal_only true -skip_via_on_pin standardcell -skip_via_on_wire_shape noshape
addRing -nets {VDD VSS} -type core_rings -follow core -layer {top M7 bottom M7 left M6 right M6} -width 2.176 -spacing 0.384 -offset 0.384 -center 0 -threshold 0 -jog_distance 0 -snap_wire_center_to_grid None
addStripe -skip_via_on_wire_shape blockring -direction horizontal -set_to_set_distance 2.16 -skip_via_on_pin Standardcell -stacked_via_top_layer M1 -layer M2 -width 0.072 -nets VDD -stacked_via_bottom_layer M1 -start_from bottom -snap_wire_center_to_grid None -start_offset -0.044 -stop_offset -0.044
addStripe -skip_via_on_wire_shape blockring -direction horizontal -set_to_set_distance 2.16 -skip_via_on_pin Standardcell -stacked_via_top_layer M1 -layer M2 -width 0.072 -nets VSS -stacked_via_bottom_layer M1 -start_from bottom -snap_wire_center_to_grid None -start_offset 1.036 -stop_offset -0.044
addStripe -skip_via_on_wire_shape Noshape -set_to_set_distance 12.960 -skip_via_on_pin Standardcell -stacked_via_top_layer Pad -spacing 0.360 -xleft_offset 0.360 -layer M3 -width 0.936 -nets {VDD VSS} -stacked_via_bottom_layer M2 -start_from left
addStripe -skip_via_on_wire_shape Noshape -direction horizontal -set_to_set_distance 21.6 -skip_via_on_pin Standardcell -stacked_via_top_layer M7 -spacing 0.864 -layer M4 -width 0.864 -nets {VDD VSS} -stacked_via_bottom_layer M3 -start_from bottom
setSrouteMode -reset
setSrouteMode -viaConnectToShape noshape
sroute -connect corePin -layerChangeRange {M1(1) M7(1)} -blockPinTarget nearestTarget -floatingStripeTarget {blockring padring ring stripe ringpin blockpin followpin} -deleteExistingRoutes -allowJogging 0 -crossoverViaLayerRange {M1(1) Pad(10)} -nets {VDD VSS} -allowLayerChange 0 -targetViaLayerRange {M1(1) Pad(10)}
editPowerVia -add_vias 1 -orthogonal_only 0
verify_drc
colorizePowerMesh
setOptMode -holdTargetSlack 0.020
setOptMode -setupTargetSlack 0.020
place_opt_design
setTieHiLoMode -maxFanout 5
addTieHiLo -prefix TIE -cell {TIELOx1_ASAP7_75t_SL TIEHIx1_ASAP7_75t_SL}
checkPlace > innovus_check_place.rep
clock_opt_design
all_constraint_modes -active
set_interactive_constraint_modes [all_constraint_modes -active]
reset_propagated_clock [all_clocks]
set_propagated_clock [all_clocks]
optDesign -postCTS
optDesign -postCTS -hold
report_ccopt_clock_trees > innovus_cts_trees.rep
report_ccopt_skew_groups > innovus_cts_skew.rep
legalizePin
routeDesign
editPowerVia -delete_vias 1 -top_layer 7 -bottom_layer 6
editPowerVia -delete_vias 1 -top_layer 6 -bottom_layer 5
editPowerVia -delete_vias 1 -top_layer 5 -bottom_layer 4
editPowerVia -delete_vias 1 -top_layer 4 -bottom_layer 3
editPowerVia -delete_vias 1 -top_layer 3 -bottom_layer 2
editPowerVia -delete_vias 1 -top_layer 2 -bottom_layer 1
editPowerVia -add_vias 1
setAnalysisMode -analysisType onChipVariation
setSIMode -enable_glitch_report true
setSIMode -enable_glitch_propagation true
setSIMode -enable_delay_report true
optDesign -postRoute
optDesign -postRoute -hold
report_noise -threshold 0.2 > innovus_noise.rep
report_noise -bumpy_waveform > innovus_noise_bumpy.rep
addFiller -cell {FILLER_ASAP7_75t_L FILLERxp5_ASAP7_75t_L FILLER_ASAP7_75t_SL FILLERxp5_ASAP7_75t_SL} -prefix FILLER
verify_drc > innovus_verify_drc.rep
verifyConnectivity -type all > innovus_verify_conn.rep
report_timing -max_paths 10 -late   > innovus_timing_setup.rep
report_timing -max_paths 10 -early  > innovus_timing_hold.rep
report_area > innovus_area.rep
report_power > innovus_power.rep
summaryReport > innovus_summary.rep
set defOutLefVia 1
set defOutLefNDR 1
defOut -netlist -routing -allLayers ../outputs/systolic_top_final.def
saveNetlist ../outputs/systolic_top_final.v
write_sdf ${OUTPUT_PATH}${DESIGN}_final.sdf
saveDesign ../outputs/systolic_top_innovus.dat
gui_show_edge_number
restoreDesign ../outputs/systolic_top_innovus.dat
restoreDesign ../outputs/systolic_top_innovus.dat.dat
