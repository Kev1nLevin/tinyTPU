#######################################################
#                                                     
#  Innovus Command Logging File                     
#  Created on Mon Feb 16 00:17:43 2026                
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
set init_mmmc_file ../scripts/systolic_top_8x8.mmmc
set init_verilog ../outputs/systolic_top_8x8_netlist.v
set init_top_cell systolic_top_ARRAY_SIZE8
set init_lef_file {../techlef/asap7_tech_4x_201209.lef ../lef/scaled/asap7sc7p5t_28_L_4x_220121a.lef ../lef/scaled/asap7sc7p5t_28_SL_4x_220121a.lef}
set init_pwr_net VDD
set init_gnd_net VSS
init_design
setDesignMode -process 45
setMultiCpuUsage -localCpu 8
setDesignMode -bottomRoutingLayer 2
setDesignMode -topRoutingLayer 7
globalNetConnect VDD -type pgpin -pin VDD -inst *
globalNetConnect VSS -type pgpin -pin VSS -inst *
floorPlan -site asap7sc7p5t -d 370.42 370.42 6.21 6.21 6.21 6.21
add_tracks -snap_m1_track_to_cell_pins
setPinAssignMode -pinEditInBatch true
editPin -fixOverlap 1 -unit MICRON -spreadDirection clockwise -side Left -layer 3 -spreadType center -spacing 2.016 -pin {clk rst_n wr_en_a wr_en_b wr_row_addr[2] wr_row_addr[1] wr_row_addr[0] wr_data[7][7] wr_data[7][6] wr_data[7][5] wr_data[7][4] wr_data[7][3] wr_data[7][2] wr_data[7][1] wr_data[7][0] wr_data[6][7] wr_data[6][6] wr_data[6][5] wr_data[6][4] wr_data[6][3] wr_data[6][2] wr_data[6][1] wr_data[6][0] wr_data[5][7] wr_data[5][6] wr_data[5][5] wr_data[5][4] wr_data[5][3] wr_data[5][2] wr_data[5][1] wr_data[5][0] wr_data[4][7] wr_data[4][6] wr_data[4][5] wr_data[4][4] wr_data[4][3] wr_data[4][2] wr_data[4][1] wr_data[4][0] wr_data[3][7] wr_data[3][6] wr_data[3][5] wr_data[3][4] wr_data[3][3] wr_data[3][2] wr_data[3][1] wr_data[3][0] wr_data[2][7] wr_data[2][6] wr_data[2][5] wr_data[2][4] wr_data[2][3] wr_data[2][2] wr_data[2][1] wr_data[2][0] wr_data[1][7] wr_data[1][6] wr_data[1][5] wr_data[1][4] wr_data[1][3] wr_data[1][2] wr_data[1][1] wr_data[1][0] wr_data[0][7] wr_data[0][6] wr_data[0][5] wr_data[0][4] wr_data[0][3] wr_data[0][2] wr_data[0][1] wr_data[0][0] start rd_row_addr[2] rd_row_addr[1] rd_row_addr[0]}
editPin -fixOverlap 1 -unit MICRON -spreadDirection clockwise -side Right -layer 3 -spreadType center -spacing 1.008 -pin {busy done rd_data[7][31] rd_data[7][30] rd_data[7][29] rd_data[7][28] rd_data[7][27] rd_data[7][26] rd_data[7][25] rd_data[7][24] rd_data[7][23] rd_data[7][22] rd_data[7][21] rd_data[7][20] rd_data[7][19] rd_data[7][18] rd_data[7][17] rd_data[7][16] rd_data[7][15] rd_data[7][14] rd_data[7][13] rd_data[7][12] rd_data[7][11] rd_data[7][10] rd_data[7][9] rd_data[7][8] rd_data[7][7] rd_data[7][6] rd_data[7][5] rd_data[7][4] rd_data[7][3] rd_data[7][2] rd_data[7][1] rd_data[7][0] rd_data[6][31] rd_data[6][30] rd_data[6][29] rd_data[6][28] rd_data[6][27] rd_data[6][26] rd_data[6][25] rd_data[6][24] rd_data[6][23] rd_data[6][22] rd_data[6][21] rd_data[6][20] rd_data[6][19] rd_data[6][18] rd_data[6][17] rd_data[6][16] rd_data[6][15] rd_data[6][14] rd_data[6][13] rd_data[6][12] rd_data[6][11] rd_data[6][10] rd_data[6][9] rd_data[6][8] rd_data[6][7] rd_data[6][6] rd_data[6][5] rd_data[6][4] rd_data[6][3] rd_data[6][2] rd_data[6][1] rd_data[6][0] rd_data[5][31] rd_data[5][30] rd_data[5][29] rd_data[5][28] rd_data[5][27] rd_data[5][26] rd_data[5][25] rd_data[5][24] rd_data[5][23] rd_data[5][22] rd_data[5][21] rd_data[5][20] rd_data[5][19] rd_data[5][18] rd_data[5][17] rd_data[5][16] rd_data[5][15] rd_data[5][14] rd_data[5][13] rd_data[5][12] rd_data[5][11] rd_data[5][10] rd_data[5][9] rd_data[5][8] rd_data[5][7] rd_data[5][6] rd_data[5][5] rd_data[5][4] rd_data[5][3] rd_data[5][2] rd_data[5][1] rd_data[5][0] rd_data[4][31] rd_data[4][30] rd_data[4][29] rd_data[4][28] rd_data[4][27] rd_data[4][26] rd_data[4][25] rd_data[4][24] rd_data[4][23] rd_data[4][22] rd_data[4][21] rd_data[4][20] rd_data[4][19] rd_data[4][18] rd_data[4][17] rd_data[4][16] rd_data[4][15] rd_data[4][14] rd_data[4][13] rd_data[4][12] rd_data[4][11] rd_data[4][10] rd_data[4][9] rd_data[4][8] rd_data[4][7] rd_data[4][6] rd_data[4][5] rd_data[4][4] rd_data[4][3] rd_data[4][2] rd_data[4][1] rd_data[4][0] rd_data[3][31] rd_data[3][30] rd_data[3][29] rd_data[3][28] rd_data[3][27] rd_data[3][26] rd_data[3][25] rd_data[3][24] rd_data[3][23] rd_data[3][22] rd_data[3][21] rd_data[3][20] rd_data[3][19] rd_data[3][18] rd_data[3][17] rd_data[3][16] rd_data[3][15] rd_data[3][14] rd_data[3][13] rd_data[3][12] rd_data[3][11] rd_data[3][10] rd_data[3][9] rd_data[3][8] rd_data[3][7] rd_data[3][6] rd_data[3][5] rd_data[3][4] rd_data[3][3] rd_data[3][2] rd_data[3][1] rd_data[3][0] rd_data[2][31] rd_data[2][30] rd_data[2][29] rd_data[2][28] rd_data[2][27] rd_data[2][26] rd_data[2][25] rd_data[2][24] rd_data[2][23] rd_data[2][22] rd_data[2][21] rd_data[2][20] rd_data[2][19] rd_data[2][18] rd_data[2][17] rd_data[2][16] rd_data[2][15] rd_data[2][14] rd_data[2][13] rd_data[2][12] rd_data[2][11] rd_data[2][10] rd_data[2][9] rd_data[2][8] rd_data[2][7] rd_data[2][6] rd_data[2][5] rd_data[2][4] rd_data[2][3] rd_data[2][2] rd_data[2][1] rd_data[2][0] rd_data[1][31] rd_data[1][30] rd_data[1][29] rd_data[1][28] rd_data[1][27] rd_data[1][26] rd_data[1][25] rd_data[1][24] rd_data[1][23] rd_data[1][22] rd_data[1][21] rd_data[1][20] rd_data[1][19] rd_data[1][18] rd_data[1][17] rd_data[1][16] rd_data[1][15] rd_data[1][14] rd_data[1][13] rd_data[1][12] rd_data[1][11] rd_data[1][10] rd_data[1][9] rd_data[1][8] rd_data[1][7] rd_data[1][6] rd_data[1][5] rd_data[1][4] rd_data[1][3] rd_data[1][2] rd_data[1][1] rd_data[1][0] rd_data[0][31] rd_data[0][30] rd_data[0][29] rd_data[0][28] rd_data[0][27] rd_data[0][26] rd_data[0][25] rd_data[0][24] rd_data[0][23] rd_data[0][22] rd_data[0][21] rd_data[0][20] rd_data[0][19] rd_data[0][18] rd_data[0][17] rd_data[0][16] rd_data[0][15] rd_data[0][14] rd_data[0][13] rd_data[0][12] rd_data[0][11] rd_data[0][10] rd_data[0][9] rd_data[0][8] rd_data[0][7] rd_data[0][6] rd_data[0][5] rd_data[0][4] rd_data[0][3] rd_data[0][2] rd_data[0][1] rd_data[0][0]}
editPin -snap TRACK -pin *
setPinAssignMode -pinEditInBatch false
legalizePin
setAddRingMode -ring_target default -extend_over_row 0 -ignore_rows 0 -stacked_via_top_layer M7 -stacked_via_bottom_layer M1
addRing -nets {VDD VSS} -type core_rings -layer {top M7 bottom M7 left M6 right M6} -width {top 1.800 bottom 1.800 left 1.800 right 1.800} -spacing {top 0.900 bottom 0.900 left 0.900 right 0.900} -offset {top 0.900 bottom 0.900 left 0.900 right 0.900}
setAddStripeMode -ignore_block_check false -break_at none -route_over_rows_only false -rows_without_stripes_only false -stacked_via_top_layer M4 -stacked_via_bottom_layer M1
addStripe -nets {VDD VSS} -layer M3 -direction vertical -width 0.072 -spacing 0.936 -set_to_set_distance 12.960 -start_from left -start_offset 6.480
addStripe -nets {VDD VSS} -layer M4 -direction horizontal -width 1.152 -spacing 0.576 -set_to_set_distance 12.960 -start_from bottom -start_offset 6.480
sroute -connect {blockPin padPin padRing corePin floatingStripe} -layerChangeRange {M1 M4} -blockPinTarget {nearestRingStripe nearestTarget} -padPinPortConnect {allPort oneGeom} -checkAlignedSecondaryPin 1 -allowJogging 1 -crossoverViaLayerRange {M1 M4} -allowLayerChange 0 -targetViaLayerRange {M1 M4}
verify_drc > innovus_8x8_pre_route_geom.rpt
checkPlace > innovus_8x8_check_place.rep
setOptMode -opt_hold_target_slack 0.02
setOptMode -opt_setup_target_slack 0.02
place_opt_design
setTieHiLoMode -maxFanout 5
addTieHiLo -prefix TIE -cell {TIELOx1_ASAP7_75t_SL TIEHIx1_ASAP7_75t_SL}
checkPlace > innovus_8x8_check_place_post.rep
clock_opt_design
all_constraint_modes -active
set_interactive_constraint_modes [all_constraint_modes -active]
reset_propagated_clock [all_clocks]
set_propagated_clock [all_clocks]
optDesign -postCTS
optDesign -postCTS -hold
report_ccopt_clock_trees > innovus_8x8_cts_trees.rep
report_ccopt_skew_groups > innovus_8x8_cts_skew.rep
setNanoRouteMode -routeWithSiDriven true
setNanoRouteMode -routeWithTimingDriven true
routeDesign -globalDetail
editPowerVia -delete_vias 1
editPowerVia -bottom_layer M1 -top_layer M4 -add_vias 1
setAnalysisMode -analysisType onChipVariation -cppr both
optDesign -postRoute
optDesign -postRoute -hold
optDesign -postRoute -si
win
zoomBox -336.71475 -197.06650 1034.16350 506.92025
zoomBox -191.98300 -34.52150 649.90775 397.81450
zoomBox -128.06275 37.26575 480.20325 349.62850
zoomBox 23.43450 150.26275 252.84225 268.07050
zoomBox 81.94650 192.10575 168.46825 236.53725
zoomBox 98.88175 204.21675 144.04700 227.41050
zoomBox 68.33675 182.37325 188.09225 243.87125
zoomBox 6.85275 138.40425 276.75200 277.00550
zoomBox -132.93750 38.49575 475.34800 350.86850
fit
zoomBox 121.83375 157.96125 473.84425 338.72900
zoomBox 249.31750 224.02975 433.06975 318.39200
zoomBox 318.16050 273.38800 399.69300 315.25725
zoomBox 338.95900 288.06425 389.03050 313.77750
zoomBox 356.34475 300.19075 378.56225 311.60000
zoomBox 364.98150 306.20625 373.36150 310.50975
selectObject IO_Pin {rd_data[7][28]}
zoomBox 353.24550 299.21275 379.38825 312.63775
zoomBox 305.23075 273.20975 401.17175 322.47825
zoomBox 222.26725 228.58150 438.49450 339.62075
zoomBox 35.28750 128.00075 522.61075 378.25575
zoomBox -24.02725 96.09400 549.29450 390.51175
deselectAll
selectWire 232.0920 299.5920 232.1640 300.4560 3 {u_array_gen_row[5].gen_col[6].u_pe_csa_tree_ADD_TC_OP_groupi_n_167}
deselectAll
selectWire 249.6600 248.5440 249.7320 251.8080 3 CTS_10
deselectAll
selectWire 298.9080 255.3120 302.7240 255.3840 2 FE_OFN6283_n_6152
zoomBox -176.83225 21.94250 616.69275 429.44125
zoomBox -266.17425 -11.15025 667.38450 468.26000
deselectAll
fit
setDelayCalMode -engine default -siAware true
optDesign -postRoute
optDesign -postRoute -hold
addFiller -cell {DECAPx10_ASAP7_75t_SL DECAPx6_ASAP7_75t_SL DECAPx4_ASAP7_75t_SL DECAPx2_ASAP7_75t_SL DECAPx1_ASAP7_75t_SL FILLER_ASAP7_75t_SL FILLERxp5_ASAP7_75t_SL DECAPx10_ASAP7_75t_L DECAPx6_ASAP7_75t_L DECAPx4_ASAP7_75t_L DECAPx2_ASAP7_75t_L DECAPx1_ASAP7_75t_L FILLER_ASAP7_75t_L FILLERxp5_ASAP7_75t_L} -prefix FILLER
ecoRoute -fix_drc
verify_drc > innovus_8x8_final_geom.rpt
report_timing -machine_readable -max_paths 20 -nworst 1 > innovus_8x8_timing_setup.rep
report_timing -machine_readable -max_paths 20 -nworst 1 -late > innovus_8x8_timing_hold.rep
report_area > innovus_8x8_area.rep
report_power > innovus_8x8_power.rep
summaryReport > innovus_8x8_summary.rep
defOut -floorplan -netlist -routing ../outputs/systolic_top_8x8_final.def
saveNetlist ../outputs/systolic_top_8x8_final.v
write_sdf ../outputs/systolic_top_8x8_final.sdf
saveDesign ../outputs/systolic_top_8x8_innovus.dat
zoomBox -379.49200 -136.86225 912.33425 526.52900
zoomBox -73.54275 63.64700 499.64800 357.99750
zoomBox 55.49775 116.18350 309.82575 246.78850
zoomBox 70.93625 122.46900 287.11525 233.48325
zoomBox 122.93050 151.39475 218.85050 200.65250
zoomBox 145.96800 164.19700 188.52875 186.05325
zoomBox 148.72425 165.72875 184.90100 184.30650
zoomBox 158.45275 171.13500 172.09675 178.14150
zoomBox 161.72925 172.95550 167.78400 176.06475
zoomBox 156.18825 169.87625 175.07625 179.57575
zoomBox 138.90475 160.27175 197.82350 190.52825
zoomBox 70.98675 122.24550 287.21225 233.28375
zoomBox -83.18700 35.92525 490.12875 330.34000
zoomBox -309.84600 -90.97850 788.44725 473.02775
zoomBox -238.71800 -51.15475 694.83150 428.25075
zoomBox -178.25925 -17.30450 615.25800 390.19025
zoomBox -126.86925 11.46825 547.62050 357.83875
setLayerPreference violation -isVisible 0
fit
selectInst {u_array_gen_row[3].gen_col[5].u_pe_csa_tree_ADD_TC_OP_groupi_g2551}
deselectAll
selectInst FILLER_T_4_8831
deselectAll
selectInst {u_array_gen_row[2].gen_col[3].u_pe_u_mac_acc_reg_reg[4]}
deselectAll
selectInst FILLER_T_0_5167
deselectAll
selectWire 303.2280 174.1680 303.3000 227.0160 3 TIE_LTIEHI_713_NET
deselectAll
selectInst FE_RC_169_0
deselectAll
selectWire 151.0200 200.2320 151.0920 203.1120 3 FE_OFN12920_u_array_b_wire_1__4__3
deselectAll
selectInst g63625
deselectAll
selectWire 218.6880 158.4120 222.3840 158.5080 4 FE_OFN304_n_18
deselectAll
selectWire 313.7280 193.9320 313.8240 262.7640 5 TIE_LTIEHI_739_NET
deselectAll
selectInst {u_array_gen_row[4].gen_col[4].u_pe_csa_tree_ADD_TC_OP_groupi_g2552}
deselectAll
selectWire 237.8880 130.7640 237.9840 176.1720 5 TIE_LTIEHI_576_NET
deselectAll
selectInst FILLER_T_4_7334
deselectAll
selectInst TIE_LTIEHI_76
zoomBox -28.35850 120.20575 225.96925 250.81050
zoomBox 38.03500 170.50025 96.94200 200.75075
zoomBox 51.63175 180.80050 70.51675 190.49850
zoomBox 55.20075 183.50375 63.58100 187.80725
zoomBox 56.29925 184.33575 61.44575 186.97875
zoomBox 57.38775 185.16050 59.32925 186.15750
zoomBox 57.64225 185.35325 58.83450 185.96550
deselectAll
selectWire 58.1760 149.5800 58.2720 217.8360 5 TIE_LTIEHI_137_NET
deselectAll
selectWire 58.1400 184.9200 58.2120 185.9760 3 CTS_71
deselectAll
selectWire 57.9840 152.8440 58.0800 205.3560 5 TIE_LTIEHI_129_NET
deselectAll
selectInst {mat_b_reg[2][0][0]}
zoomBox 56.43825 184.40375 60.81325 186.65050
zoomBox 54.37925 182.76400 64.24075 187.82825
zoomBox 47.65575 177.52275 73.80425 190.95075
zoomBox 24.45850 159.27500 106.02800 201.16325
zoomBox -6.98125 134.48225 149.28000 214.72700
zoomBox -48.31000 101.89175 206.13600 232.55725
zoomBox -89.50525 69.45275 262.66925 250.30475
zoomBox -182.78200 -3.99775 390.67550 290.48975
zoomBox -233.77300 -76.44500 559.93975 331.15000
deselectAll
zoomBox -377.50150 -166.02625 721.06300 398.11925
fit
zoomBox -34.47850 206.99500 264.73100 360.64800
zoomBox 32.19925 291.93975 145.04625 349.89000
zoomBox 57.34650 323.97650 99.90725 345.83275
zoomBox 59.63075 326.88650 95.80725 345.46425
zoomBox 67.69200 337.15700 81.33650 344.16375
zoomBox 70.40750 340.61650 76.46175 343.72550
selectWire 6.1920 343.1160 364.1040 343.1880 1 VDD
zoomBox 65.76450 335.89300 84.65200 345.59225
zoomBox 51.17700 321.18500 110.09525 351.44125
zoomBox 5.65700 275.60050 189.44675 369.98200
zoomBox -105.49475 167.63625 381.81825 417.88600
zoomBox -217.62500 58.82025 575.88300 466.31025
deselectAll
fit
setLayerPreference violation -isVisible 1
zoomBox 159.30775 25.33375 413.63625 155.93900
zoomBox 280.87775 40.25350 362.41050 82.12300
zoomBox 318.17025 50.00600 344.30875 63.42900
zoomBox 332.02025 52.80550 340.40000 57.10875
zoomBox 332.94375 53.05650 340.06675 56.71425
zoomBox 335.85225 53.81925 339.01300 55.44250
zoomBox 337.04975 54.19825 338.06375 54.71900
zoomBox 337.29125 54.26375 337.91450 54.58375
selectMarker 337.6080 54.3600 337.6800 54.3960 3 1 26
deselectAll
selectMarker 337.6080 54.3600 337.6800 54.3960 3 1 26
deselectAll
selectMarker 337.6800 54.3600 337.7520 54.3960 3 1 26
zoomBox 336.57350 54.06650 338.22675 54.91550
zoomBox 334.13100 53.39650 339.28900 56.04525
zoomBox 326.51150 51.31200 342.60200 59.57500
zoomBox 302.76250 45.28800 352.95575 71.06375
zoomBox 228.24950 25.80500 384.82275 106.21000
zoomBox 45.43225 -27.09275 460.58300 186.09950
zoomBox -376.02750 -163.86775 559.61875 316.61450
zoomBox -514.33425 -204.07900 586.42625 361.19425
zoomBox -1553.29100 -686.99425 1365.34125 811.81025
zoomBox -608.70275 -207.73250 686.30975 457.29500
fit
setLayerPreference violation -isVisible 0
deselectAll
fit
fit
fit
fit
