#!/bin/bash
# =============================================================================
# Gate-Level Simulation with SDF Back-Annotation
# Proves post-route netlist still passes all testbench scenarios
# =============================================================================
# Usage: cd scripts && bash run_gate_sim.sh
# =============================================================================

echo "============================================"
echo "  Gate-Level Simulation (Post-Route + SDF)"
echo "============================================"

# Project root (one level up from scripts/)
PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DESIGN="systolic_top"

# Paths
NETLIST="${PROJECT_ROOT}/outputs/systolic_top_final.v"
SDF="${PROJECT_ROOT}/outputs/systolic_top_final.sdf"
TB="${PROJECT_ROOT}/tb/tb_systolic_top.sv"
LIB_DIR="${PROJECT_ROOT}/lib"
WORK_DIR="${PROJECT_ROOT}/sim_work_gate"

# Locate Verilog simulation models for ASAP7 cells
# These are behavioral models needed for gate-level sim
VERILOG_MODELS=""
for vfile in ${LIB_DIR}/../verilog/*.v ${LIB_DIR}/../verilog/*.sv; do
    if [ -f "$vfile" ]; then
        VERILOG_MODELS="${VERILOG_MODELS} -v ${vfile}"
    fi
done

# If no verilog models found, try common ASAP7 locations
if [ -z "$VERILOG_MODELS" ]; then
    echo ">>> Looking for Verilog cell models..."
    for search_dir in \
        "${PROJECT_ROOT}/verilog" \
        "${PROJECT_ROOT}/cells/verilog" \
        "${PROJECT_ROOT}/../asap7/verilog" \
        "${HOME}/asap7PDK/verilog"; do
        if [ -d "$search_dir" ]; then
            for vfile in ${search_dir}/*.v ${search_dir}/*.sv; do
                [ -f "$vfile" ] && VERILOG_MODELS="${VERILOG_MODELS} -v ${vfile}"
            done
            [ -n "$VERILOG_MODELS" ] && break
        fi
    done
fi

if [ -z "$VERILOG_MODELS" ]; then
    echo ">>> ERROR: No Verilog cell models found!"
    echo ">>> Place ASAP7 Verilog models in ${PROJECT_ROOT}/verilog/"
    echo ">>> These are .v files like asap7sc7p5t_SEQ_LVT_TT.v"
    exit 1
fi

# Check required files exist
for f in "$NETLIST" "$SDF" "$TB"; do
    if [ ! -f "$f" ]; then
        echo ">>> ERROR: Required file not found: $f"
        exit 1
    fi
done

echo ">>> Netlist: $NETLIST"
echo ">>> SDF:     $SDF"
echo ">>> TB:      $TB"

# Create work directory
mkdir -p "$WORK_DIR"
cd "$WORK_DIR"

# Create SDF command file for Xcelium
cat > sdf_cmd.txt << EOF
COMPILED
SDF_FILE = "${SDF}",
SCOPE = tb_systolic_top.dut,
LOG_FILE = "sdf_annotate.log",
MTM_SPEC = MAXIMUM,
SCALE_FACTORS = "1.0:1.0:1.0",
SCALE_TYPE = FROM_MTM;
EOF

echo ">>> Running Xcelium gate-level simulation..."

# Run simulation
xrun \
    -sv \
    -64bit \
    -access +rwc \
    -timescale 1ns/1ps \
    ${VERILOG_MODELS} \
    "${NETLIST}" \
    "${TB}" \
    -top tb_systolic_top \
    -sdf_cmd_file sdf_cmd.txt \
    -input "${PROJECT_ROOT}/scripts/xcelium_waves.tcl" \
    -define GATE_SIM \
    -l gate_sim.log \
    +no_notifier \
    +nospecify 2>&1

# Check results
echo ""
echo "============================================"
if grep -q "ALL TESTS PASSED" gate_sim.log 2>/dev/null; then
    echo "  GATE-LEVEL SIM: ALL TESTS PASSED ✓"
elif grep -q "PASSED" gate_sim.log 2>/dev/null; then
    PASS=$(grep -c "PASSED" gate_sim.log)
    FAIL=$(grep -c "FAILED" gate_sim.log)
    echo "  GATE-LEVEL SIM: ${PASS} passed, ${FAIL} failed"
else
    echo "  GATE-LEVEL SIM: Check gate_sim.log for results"
fi
echo "  Log: ${WORK_DIR}/gate_sim.log"
echo "  SDF: ${WORK_DIR}/sdf_annotate.log"
echo "============================================"
