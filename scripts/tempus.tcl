# =============================================================================
# Cadence Tempus (SSV) Signoff Static Timing Analysis
# Design: systolic_top (4x4 Systolic Array MAC Accelerator)
# Target: ASAP7 7nm PDK
# =============================================================================
# Usage: cd STA && tempus -init ../scripts/tempus.tcl |& tee tempus_run.log
# =============================================================================

puts "============================================"
puts "  Tempus Signoff STA: Systolic Array MAC"
puts "  Target: ASAP7 7nm"
puts "============================================"

# =============================================================================
# 1. Load Design from Files (not restoreDesign — avoids version mismatch)
# =============================================================================
set DESIGN       systolic_top
set BASE         [file normalize [pwd]/..]

set init_design_uniquify  1
set init_design_netlisttype Verilog
set init_design_settop    1
set init_verilog          ${BASE}/outputs/systolic_top_final.v
set init_top_cell         ${DESIGN}
set init_pwr_net          VDD
set init_gnd_net          VSS

set init_lef_file [list \
    ${BASE}/techlef/asap7_tech_4x_201209.lef \
    ${BASE}/lef/scaled/asap7sc7p5t_28_L_4x_220121a.lef \
    ${BASE}/lef/scaled/asap7sc7p5t_28_SL_4x_220121a.lef \
]

set init_mmmc_file        ${BASE}/scripts/systolic_top.mmmc

init_design
puts ">>> Design initialized."

# Read physical layout (placement + routing)
set DEF_FILE ${BASE}/outputs/systolic_top_final.def
if {[file exists $DEF_FILE]} {
    defIn $DEF_FILE
    puts ">>> DEF loaded: $DEF_FILE"
} else {
    puts ">>> ERROR: DEF not found at $DEF_FILE"
    exit 1
}

# =============================================================================
# 2. Signoff Settings
# =============================================================================

# Process mode (matches Innovus — no QRC, use LEF-based extraction)
setDesignMode -process 45

# Enable SI-aware analysis
setAnalysisMode -analysisType onChipVariation
setAnalysisMode -cppr both

# Delay calculation
setDelayCalMode -siAware true
setDelayCalMode -engine aae

# Extraction
setExtractRCMode -engine postRoute
setExtractRCMode -effortLevel medium

puts ">>> Signoff settings configured."

# =============================================================================
# 3. Post-Route Extraction
# =============================================================================
puts ">>> Running post-route extraction..."

extractRC

puts ">>> Extraction complete."

# =============================================================================
# 4. Setup Timing Analysis
# =============================================================================
puts ">>> Running setup timing analysis..."

setAnalysisMode -checkType setup
update_timing -full

report_timing -max_paths 20 -path_type full_clock_expanded \
    -late > tempus_timing_setup.rep

report_timing_summary > tempus_summary_setup.rep

puts ">>> Setup analysis complete."

# =============================================================================
# 5. Hold Timing Analysis
# =============================================================================
puts ">>> Running hold timing analysis..."

setAnalysisMode -checkType hold
update_timing -full

report_timing -max_paths 20 -path_type full_clock_expanded \
    -early > tempus_timing_hold.rep

report_timing_summary > tempus_summary_hold.rep

puts ">>> Hold analysis complete."

# =============================================================================
# 6. Path-Based Analysis (PBA) — more accurate than graph-based
# =============================================================================
puts ">>> Running path-based analysis..."

setAnalysisMode -checkType setup
report_timing -max_paths 10 -path_type full_clock_expanded \
    -pba_mode path -late > tempus_timing_setup_pba.rep

setAnalysisMode -checkType hold
report_timing -max_paths 10 -path_type full_clock_expanded \
    -pba_mode path -early > tempus_timing_hold_pba.rep

puts ">>> PBA complete."

# =============================================================================
# 7. Violation & Coverage Reports
# =============================================================================

report_constraint -all_violators > tempus_violations.rep
report_analysis_coverage > tempus_coverage.rep
report_clocks > tempus_clocks.rep

# =============================================================================
# 8. SI / Noise Analysis
# =============================================================================
puts ">>> Running SI analysis..."

if {[catch {report_noise -threshold 0.2 > tempus_noise.rep} err]} {
    puts ">>> Note: Noise report skipped ($err)"
}

# =============================================================================
# 9. Power Analysis
# =============================================================================
puts ">>> Running power analysis..."

if {[catch {report_power > tempus_power.rep} err]} {
    puts ">>> Note: Power report skipped ($err)"
}

# =============================================================================
# 10. Summary
# =============================================================================
puts ""
puts "============================================"
puts "  Tempus Signoff STA Complete"
puts "============================================"
puts "  Reports in STA/:"
puts ""
puts "  tempus_timing_setup.rep"
puts "  tempus_timing_hold.rep"
puts "  tempus_timing_setup_pba.rep"
puts "  tempus_timing_hold_pba.rep"
puts "  tempus_summary_setup.rep"
puts "  tempus_summary_hold.rep"
puts "  tempus_violations.rep"
puts "============================================"

win
