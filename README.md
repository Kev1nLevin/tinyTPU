# 4×4 Systolic Array — Neural Network MAC Accelerator

## RTL-to-GDS | Cadence Flow | ASAP7 7nm PDK

![Flow](https://img.shields.io/badge/Flow-RTL%20to%20GDS-brightgreen)
![PDK](https://img.shields.io/badge/PDK-ASAP7%207nm-blue)
![Tools](https://img.shields.io/badge/Tools-Cadence%20Genus%20%2B%20Innovus-orange)
![Timing](https://img.shields.io/badge/Timing-Met%20✓-success)

---

## Overview

A fully synthesizable **4×4 output-stationary systolic array** for INT8 matrix multiplication, targeting neural network inference acceleration. The design is implemented through the complete **RTL-to-GDS** physical design flow using Cadence tools on the **ASAP7 7nm** FinFET PDK.

### Key Results

| Parameter              | Value                          |
|------------------------|--------------------------------|
| Array Dimensions       | 4 × 4 (16 PEs)                |
| Input Precision        | INT8 (signed)                  |
| Accumulator Width      | 32-bit                         |
| Dataflow               | Output-Stationary              |
| Clock Frequency        | **667 MHz**                    |
| Technology             | ASAP7 7nm FinFET               |
| Peak Throughput        | **10.67 GOPS**                 |
| Latency (4×4 matmul)   | 7 clock cycles                |
| Setup WNS             | **+21 ps** (timing met ✓)      |
| Hold WNS              | **+79 ps** (timing met ✓)      |
| Total Power            | **4.57 mW**                    |
| Die Area               | 192.8 × 192.8 µm              |
| Cell Count             | 8,228 standard cells           |
| Placement Density      | 56.9%                          |

---

## Architecture

```
              Weight Columns (A matrix, top-to-bottom)
                 ↓        ↓        ↓        ↓
              a_col[0] a_col[1] a_col[2] a_col[3]
                 |        |        |        |
  b_row[0] → [PE00] → [PE01] → [PE02] → [PE03] →   Activation
  b_row[1] → [PE10] → [PE11] → [PE12] → [PE13] →   Rows
  b_row[2] → [PE20] → [PE21] → [PE22] → [PE23] →   (B matrix,
  b_row[3] → [PE30] → [PE31] → [PE32] → [PE33] →   left-to-right)
                 |        |        |        |
                 ↓        ↓        ↓        ↓

  Each PE: acc += a_in * b_in (MAC operation)
  Weights flow vertically, activations flow horizontally
  Results accumulate in-place (output-stationary)
```

### Block Diagram

```
  ┌──────────────────────────────────────────────┐
  │                 systolic_top                   │
  │                                                │
  │  ┌─────────┐    ┌───────────┐    ┌──────────┐ │
  │  │ Matrix A │    │   Skew    │    │          │ │
  │  │ Reg File │───▶│Controller │───▶│          │ │
  │  └─────────┘    │   (A)     │    │  4x4     │ │
  │                 └───────────┘    │ Systolic  │ │
  │  ┌─────────┐    ┌───────────┐    │  Array   │ │
  │  │ Matrix B │    │   Skew    │    │          │ │
  │  │ Reg File │───▶│Controller │───▶│ (16 PEs) │ │
  │  └─────────┘    │   (B)     │    │          │ │
  │                 └───────────┘    └────┬─────┘ │
  │  ┌───────────┐                        │       │
  │  │   FSM     │── control signals ────▶│       │
  │  │Controller │                   Result[4][4] │
  │  └───────────┘                        ▼       │
  └──────────────────────────────────────────────┘
```

---

## Module Hierarchy

```
systolic_top                          (598 lines SystemVerilog)
├── systolic_controller               FSM: IDLE→CLEAR→LOAD→DRAIN→DONE
├── input_skew_controller (×2)        Skew registers for A and B
└── systolic_array_4x4                4×4 PE mesh
    └── processing_element (×16)      Data flow + MAC
        └── mac_unit                  8b×8b multiply + 32b accumulate
```

---

## Project Structure

```
Neural_Network_Accelerator/
├── rtl/
│   ├── mac_unit.sv                 # Multiply-accumulate unit
│   ├── processing_element.sv       # PE with systolic registers
│   ├── systolic_array_4x4.sv      # 4×4 PE array interconnect
│   ├── input_skew_controller.sv   # Input staggering logic
│   ├── systolic_controller.sv     # FSM controller
│   └── systolic_top.sv            # Top-level integration
├── tb/
│   └── tb_systolic_top.sv         # Testbench (5 tests + golden model)
├── scripts/
│   ├── run_sim.sh                 # Xcelium RTL simulation
│   ├── xcelium_waves.tcl          # Waveform dump config
│   ├── syn_systolic.tcl           # Genus synthesis script
│   ├── innovus.tcl                # Innovus P&R script
│   └── systolic_top.mmmc          # MMMC timing configuration
├── lib/                           # ASAP7 .lib timing libraries (not tracked)
├── lef/                           # ASAP7 LEF physical libraries (not tracked)
├── syn/                           # Genus synthesis working directory
├── PnR/
│   ├── run/                       # Innovus working directory + reports
│   └── scripts/                   # P&R scripts (symlinked)
├── outputs/                       # Final deliverables (DEF, netlist, SDF)
├── Makefile
└── README.md
```

---

## Tool Flow

```
   SystemVerilog RTL
        │
        ▼
   ┌──────────┐    Cadence Xcelium
   │ Simulate  │──────────────────── 5/5 tests passed ✓
   └──────────┘
        │
        ▼
   ┌──────────┐    Cadence Genus
   │ Synthesis │──────────────────── 7,888 cells, 17,406 µm², 5.14 mW
   └──────────┘                      Explored 1 GHz / 833 MHz / 667 MHz
        │
        ▼
   ┌──────────┐    Cadence Innovus
   │   P & R   │──────────────────── Floorplan → Place → CTS → Route
   └──────────┘                      Setup: +21ps ✓  Hold: +79ps ✓
        │
        ▼
   ┌──────────┐    Post-Route Optimization + SI Analysis
   │ Signoff   │──────────────────── 0 DRV, 0 glitch, 4.57 mW
   └──────────┘
        │
        ▼
      DEF + Netlist + SDF
```

---

## Physical Design Results

### Timing (Post-Route + SI)

| Mode  | WNS (ns) | TNS (ns) | Violating Paths |
|-------|-----------|-----------|-----------------|
| Setup | **+0.021**| 0.000     | 0               |
| Hold  | **+0.079**| 0.000     | 0               |

- 0 design rule violations (max_cap, max_tran, max_fanout)
- 0 glitch violations (signal integrity clean)
- 0.00% H / 0.01% V routing overflow

### Power Breakdown (667 MHz, TT corner)

| Component     | Power (mW) | Percentage |
|---------------|------------|------------|
| Internal      | 2.238      | 48.9%      |
| Switching     | 2.230      | 48.8%      |
| Leakage       | 0.105      | 2.3%       |
| **Total**     | **4.572**  | **100%**   |

| Group         | Power (mW) | Percentage |
|---------------|------------|------------|
| Combinational | 2.449      | 53.6%      |
| Sequential    | 1.477      | 32.3%      |
| Clock Tree    | 0.646      | 14.1%      |

### Synthesis → P&R Comparison

| Metric       | Synthesis | Post-P&R  |
|--------------|-----------|-----------|
| Clock period | 1500 ps   | 1500 ps   |
| Setup WNS   | 0 ps      | +21 ps    |
| Cell count   | 7,888     | 8,228     |
| Total power  | 5.14 mW   | 4.57 mW   |

---

## Verification

5 automated tests with golden model comparison — **all passing**:

| Test | Description                  | Purpose                              |
|------|------------------------------|--------------------------------------|
| 1    | Identity matrix multiply     | Basic sanity (A × I = A)             |
| 2    | Known small values           | Hand-verifiable correctness          |
| 3    | Random matrices              | Golden model comparison              |
| 4    | Back-to-back computation     | Accumulator clearing between runs    |
| 5    | Signed (negative) numbers    | Verify signed arithmetic paths       |

---

## Prerequisites

- **Cadence Xcelium** — RTL simulation
- **Cadence Genus** — Logic synthesis
- **Cadence Innovus** — Place & route
- **ASAP7 7nm PDK** — [GitHub](https://github.com/The-OpenROAD-Project/asap7)

## Quick Start

```bash
# 1. Update ASAP7 library paths in scripts/

# 2. RTL simulation
cd scripts && source run_sim.sh

# 3. Synthesis
cd syn && genus -f ../scripts/syn_systolic.tcl

# 4. Place & Route
cd PnR/run && innovus -init ../scripts/innovus.tcl

# 5. View completed layout
cd PnR/run && innovus
innovus> restoreDesign ../outputs/systolic_top_innovus.dat.dat
```

---

## Design Decisions

1. **Output-Stationary Dataflow** — Minimizes result data movement. Each PE accumulates its own C[i][j]. Best for inference where weight reuse is high.

2. **INT8 Inputs / INT32 Accumulator** — Matches industry practice (Google TPU v1). 32-bit accumulator prevents overflow for 4×4 dot products (max: 4 × 127² = 64,516).

3. **Skewed Input Feeding** — Classic systolic technique. Each row/column is delayed by its index to align partial products correctly.

4. **Simple FSM Controller** — 5-state machine keeps control logic minimal and verifiable.

5. **ASAP7 LVT + SLVT cells** — Multi-Vt optimization for performance/leakage tradeoff at 7nm.

6. **667 MHz target** — Explored 1 GHz (too aggressive), 833 MHz (marginal), settled on 667 MHz with comfortable timing margin.

---

## Future Work

- Scale to 8×8 or 16×16 array (`ARRAY_SIZE` parameter)
- Add ReLU activation function
- AXI4-Lite bus interface for SoC integration
- FP16/BF16 precision support
- Signoff STA with Cadence Tempus (SSV)
- QRC parasitic extraction for signoff-quality timing
- Gate-level simulation with SDF back-annotation

---

## License

Released for educational and portfolio purposes.
