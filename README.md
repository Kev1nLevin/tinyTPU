# tinyTPU — Scalable Systolic Array Neural Network Accelerator

## RTL-to-GDS | Cadence Flow | ASAP7 7nm PDK

[![Flow](https://img.shields.io/badge/Flow-RTL%20to%20GDS-brightgreen)](.)
[![PDK](https://img.shields.io/badge/PDK-ASAP7%207nm-blue)](.)
[![Tools](https://img.shields.io/badge/Tools-Cadence%20Genus%20%2B%20Innovus-orange)](.)
[![Timing](https://img.shields.io/badge/Timing-Met%20%E2%9C%93-success)](.)

---

## Overview

A fully synthesizable **parameterized output-stationary systolic array** for INT8 matrix multiplication, targeting neural network inference acceleration. The design is implemented through the complete **RTL-to-GDS** physical design flow using Cadence tools on the **ASAP7 7nm** FinFET PDK.

Both **4×4** and **8×8** array configurations have been taken through the full P&R flow and are timing-clean at **667 MHz**.

---

## Key Results at a Glance

| Parameter | 4×4 Array | 8×8 Array |
|---|---|---|
| Processing Elements | 16 | 64 |
| Input Precision | INT8 (signed) | INT8 (signed) |
| Accumulator Width | 32-bit | 32-bit |
| Clock Frequency | **667 MHz** | **667 MHz** |
| Technology | ASAP7 7nm FinFET | ASAP7 7nm FinFET |
| Peak Throughput | **10.67 GOPS** | **42.67 GOPS** |
| Latency (N×N matmul) | 7 cycles | 15 cycles |
| Setup WNS | +21 ps ✓ | +21.6 ps ✓ |
| Hold WNS | +79 ps ✓ | Met ✓ |
| Total Power | **4.57 mW** | **14.05 mW** |
| Power Efficiency | **2.33 GOPS/mW** | **3.04 GOPS/mW** |
| Die Area | 192.8 × 192.8 µm | 370.4 × 370.4 µm |
| Cell Count | 8,228 | 33,560 |
| Placement Density | 56.9% | 56.6% |

> **Scaling insight:** The 8×8 array delivers **4× throughput** at only **3.07× power**, yielding a **30% improvement in power efficiency** (GOPS/mW) over the 4×4 — demonstrating favorable systolic array scaling at 7nm.

---

## Architecture

```
              Weight Columns (A matrix, top-to-bottom)
                ↓        ↓        ↓   ...   ↓
             a_col[0] a_col[1] a_col[2]  a_col[N-1]
                |        |        |         |
  b_row[0] → [PE00] → [PE01] → [PE02] → [PE0,N-1] →   Activation
  b_row[1] → [PE10] → [PE11] → [PE12] → [PE1,N-1] →   Rows
  b_row[2] → [PE20] → [PE21] → [PE22] → [PE2,N-1] →   (B matrix,
     ...        |        |        |         |           left-to-right)
  b_row[N-1]→[PEn0] → [PEn1] → [PEn2] → [PEn,N-1]→
                |        |        |         |
                ↓        ↓        ↓         ↓

  Each PE: acc += a_in * b_in (MAC operation)
  Weights flow vertically, activations flow horizontally
  Results accumulate in-place (output-stationary)
```

### Block Diagram

```
  ┌──────────────────────────────────────────────────┐
  │                  systolic_top                      │
  │              (ARRAY_SIZE = 4 or 8)                 │
  │                                                    │
  │  ┌─────────┐    ┌───────────┐    ┌──────────────┐ │
  │  │ Matrix A │    │   Skew    │    │              │ │
  │  │ Reg File │───▶│Controller │───▶│              │ │
  │  └─────────┘    │   (A)     │    │   N × N      │ │
  │                 └───────────┘    │  Systolic     │ │
  │  ┌─────────┐    ┌───────────┐    │   Array      │ │
  │  │ Matrix B │    │   Skew    │    │              │ │
  │  │ Reg File │───▶│Controller │───▶│  (N² PEs)    │ │
  │  └─────────┘    │   (B)     │    │              │ │
  │                 └───────────┘    └──────┬───────┘ │
  │  ┌───────────┐                          │         │
  │  │   FSM     │── control signals ──────▶│         │
  │  │Controller │                   Result[N][N]     │
  │  └───────────┘                          ▼         │
  └──────────────────────────────────────────────────┘
```

---

## Module Hierarchy

```
systolic_top (ARRAY_SIZE parameter)       (SystemVerilog)
├── systolic_controller                   FSM: IDLE→CLEAR→LOAD→DRAIN→DONE
├── input_skew_controller (×2)            Skew registers for A and B
└── systolic_array (N×N)                  Parameterized PE mesh
    └── processing_element (×N²)          Data flow + MAC
        └── mac_unit                      8b×8b multiply + 32b accumulate
```

---

## Physical Design Results

### 8×8 Array — Post-Route (Innovus, ASAP7 7nm)

#### Timing (667 MHz, TT corner, 0.7V, 25°C)

| Mode | WNS | Status |
|---|---|---|
| Setup | **+21.6 ps** | ✓ Met |
| Hold | **Met** | ✓ Met |

- Clock period: 1500 ps (667 MHz)
- Operating condition: PVT_0P7V_25C
- Critical path: `rd_row_addr[0]` → `rd_data[7][21]` (read-out mux logic)

#### Power Breakdown (667 MHz, 0.2 activity)

| Component | Power (mW) | Percentage |
|---|---|---|
| Internal | 9.607 | 68.4% |
| Switching | 4.010 | 28.5% |
| Leakage | 0.434 | 3.1% |
| **Total** | **14.050** | **100%** |

| Group | Power (mW) | Percentage |
|---|---|---|
| Combinational | 7.083 | 50.4% |
| Sequential | 5.385 | 38.3% |
| Clock Tree | 1.582 | 11.3% |

#### Area & Physical

| Metric | Value |
|---|---|
| Die Size | 370.42 × 370.42 µm |
| Cell Area | 73,016 µm² |
| Total Instances | 33,560 |
| Placement Density | 56.6% |
| Register Count | 4,424 flip-flops |

#### Clock Tree Synthesis

| Metric | Value |
|---|---|
| CTS Buffers | 84 |
| Clock Skew (late) | 14.4 ps |
| Skew Window | 100% occupancy (82.8–97.2 ps) |
| Max Source-Sink Length | 211.1 µm |
| CTS Violations | **0** |
| Max Leaf Fanout | 80 |
| Buffer Depth | 3 levels |

#### Synthesis → P&R Comparison (8×8)

| Metric | Synthesis (Genus) | Post-P&R (Innovus) | Delta |
|---|---|---|---|
| Clock Period | 1500 ps | 1500 ps | — |
| Setup WNS | 0 ps | +21.6 ps | Improved |
| Cell Count | 31,520 | 33,560 | +6.5% (CTS + opt) |
| Cell Area | 70,544 µm² | 73,016 µm² | +3.5% |
| Sequential | 4,424 | 4,424 | — |
| Total Power | 19.91 mW | 14.05 mW | −29.4% |
| Max Cap/Tran | 0 violations | 0 violations | — |

> **Power reduction after P&R:** The 29% power drop from synthesis to post-route is expected — Genus uses global wire-load estimates that tend to overestimate switching power, while Innovus uses extracted parasitics from actual routing. The critical path also shifts from the MAC accumulator carry chain (synthesis) to the read-out mux decode logic (post-route).

#### DRC Status

| Check | Result |
|---|---|
| Geometry DRC | 976 M3 Rect violations (ASAP7 M3 min-width; expected with 4× scaled LEF) |
| Max Cap / Tran / Fanout | 0 violations |
| Antenna | Clean |
| SI Glitch | Clean |

> **Note on M3 DRC:** The 976 M3 Rect violations are a known artifact of the ASAP7 4× scaled flow where the M3 minimum-width DRC rule is overly conservative relative to the standard-cell routing. These do not affect functionality or silicon viability in an academic PDK context.

---

### 4×4 Array — Post-Route (Innovus, ASAP7 7nm)

#### Timing (667 MHz, TT corner)

| Mode | WNS (ps) | TNS (ps) | Violating Paths |
|---|---|---|---|
| Setup | **+21** | 0.000 | 0 |
| Hold | **+79** | 0.000 | 0 |

- 0 design rule violations
- 0 glitch violations (SI clean)
- 0.00% H / 0.01% V routing overflow

#### Power Breakdown (667 MHz)

| Component | Power (mW) | Percentage |
|---|---|---|
| Internal | 2.238 | 48.9% |
| Switching | 2.230 | 48.8% |
| Leakage | 0.105 | 2.3% |
| **Total** | **4.572** | **100%** |

| Group | Power (mW) | Percentage |
|---|---|---|
| Combinational | 2.449 | 53.6% |
| Sequential | 1.477 | 32.3% |
| Clock Tree | 0.646 | 14.1% |

#### Synthesis → P&R Comparison (4×4)

| Metric | Synthesis | Post-P&R |
|---|---|---|
| Clock period | 1500 ps | 1500 ps |
| Setup WNS | 0 ps | +21 ps |
| Cell count | 7,888 | 8,228 |
| Total power | 5.14 mW | 4.57 mW |

---

## Scaling Analysis: 4×4 → 8×8

| Metric | 4×4 | 8×8 | Ratio | Ideal (4×) |
|---|---|---|---|---|
| PEs | 16 | 64 | 4.0× | 4.0× |
| Cell Count | 8,228 | 33,560 | 4.08× | 4.0× |
| Die Area | 37,172 µm² | 137,211 µm² | 3.69× | 4.0× |
| Total Power | 4.57 mW | 14.05 mW | 3.07× | 4.0× |
| Peak GOPS | 10.67 | 42.67 | 4.0× | 4.0× |
| GOPS/mW | 2.33 | 3.04 | 1.30× | 1.0× |
| GOPS/mm² | 287 | 311 | 1.08× | 1.0× |
| Flip-Flops | ~1,100 | 4,424 | 4.02× | 4.0× |
| CTS Buffers | ~20 | 84 | ~4.2× | 4.0× |

The 8×8 configuration scales near-linearly in compute while achieving **sub-linear power growth**, resulting in better efficiency at larger array sizes. This is primarily due to amortization of control logic and clock distribution overhead across more PEs.

---

## Tool Flow

```
   SystemVerilog RTL (parameterized)
        │
        ▼
   ┌──────────┐    Cadence Xcelium
   │ Simulate  │──────────────────── 5/5 tests passed ✓
   └──────────┘
        │
        ▼
   ┌──────────┐    Cadence Genus 23.14
   │ Synthesis │──────────────────── ASAP7 LVT + SLVT multi-Vt
   └──────────┘                      4×4: 7,888 cells | 8×8: 31,520 cells
        │                            Target: 667 MHz — WNS = 0 ps ✓
        ▼
   ┌──────────┐    Cadence Innovus 23.14
   │   P & R   │──────────────────── Floorplan → Place → CTS → Route
   └──────────┘                      4×4: +21ps ✓ | 8×8: +21.6ps ✓
        │                            OCV + SI-aware optimization
        ▼
   ┌──────────┐    Post-Route Opt + SI Analysis
   │ Signoff   │──────────────────── Timing met, power characterized
   └──────────┘
        │
        ▼
      DEF + Netlist + SDF
```

---

## Verification

5 automated tests with golden model comparison — **all passing**:

| Test | Description | Purpose |
|---|---|---|
| 1 | Identity matrix multiply | Basic sanity (A × I = A) |
| 2 | Known small values | Hand-verifiable correctness |
| 3 | Random matrices | Golden model comparison |
| 4 | Back-to-back computation | Accumulator clearing between runs |
| 5 | Signed (negative) numbers | Verify signed arithmetic paths |

---

## Project Structure

```
tinyTPU/
├── sources/                       # RTL source files
│   ├── mac_unit.sv                # Multiply-accumulate unit
│   ├── processing_element.sv      # PE with systolic registers
│   ├── systolic_array.sv          # Parameterized N×N PE array
│   ├── input_skew_controller.sv   # Input staggering logic
│   ├── systolic_controller.sv     # FSM controller
│   └── systolic_top.sv            # Top-level integration
├── scripts/
│   ├── syn_systolic.tcl           # Genus synthesis script
│   ├── innovus.tcl                # Innovus P&R script (4×4)
│   ├── innovus_8x8.tcl            # Innovus P&R script (8×8)
│   ├── systolic_top.mmmc          # MMMC timing config (4×4)
│   └── systolic_top_8x8.mmmc     # MMMC timing config (8×8)
├── lib/                           # ASAP7 .lib timing libraries
├── lef/                           # ASAP7 LEF physical libraries
├── techlef/                       # ASAP7 technology LEF
├── qrc/                           # RC extraction tech files
├── PnR/
│   ├── run/                       # Innovus working directory + reports
│   └── scripts/                   # P&R scripts
├── outputs/                       # Final deliverables (DEF, netlist, SDF)
├── run/                           # Simulation / synthesis working dir
└── README.md
```

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

# 3. Synthesis (set ARRAY_SIZE in TCL script)
cd run && genus -f ../scripts/syn_systolic.tcl

# 4. Place & Route — 4×4
cd PnR/run && innovus -init ../scripts/innovus.tcl

# 5. Place & Route — 8×8
cd PnR/run && innovus -init ../scripts/innovus_8x8.tcl

# 6. View completed layout
cd PnR/run && innovus
innovus> restoreDesign ../outputs/systolic_top_8x8_innovus.dat
```

---

## Design Decisions

1. **Output-Stationary Dataflow** — Minimizes result data movement. Each PE accumulates its own C[i][j]. Best for inference where weight reuse is high.
2. **INT8 Inputs / INT32 Accumulator** — Matches industry practice (Google TPU v1). 32-bit accumulator prevents overflow for N×N dot products.
3. **Skewed Input Feeding** — Classic systolic technique. Each row/column is delayed by its index to align partial products correctly.
4. **Simple FSM Controller** — 5-state machine (IDLE→CLEAR→LOAD→DRAIN→DONE) keeps control logic minimal and verifiable.
5. **ASAP7 LVT + SLVT cells** — Multi-Vt optimization for performance/leakage tradeoff at 7nm.
6. **667 MHz target** — Explored 1 GHz (too aggressive), 833 MHz (marginal), settled on 667 MHz with comfortable timing margin across both array sizes.
7. **Parameterized ARRAY_SIZE** — Single RTL codebase supports both 4×4 and 8×8 (and beyond) through the `ARRAY_SIZE` parameter.

---

## Future Work

- Scale to 16×16 array
- Add ReLU activation function
- AXI4-Lite bus interface for SoC integration
- FP16/BF16 precision support
- Signoff STA with Cadence Tempus (multi-corner multi-mode)
- QRC parasitic extraction for signoff-quality timing
- Gate-level simulation with SDF back-annotation
- Resolve remaining M3 DRC violations with tighter routing constraints

---

## License

Released for educational and portfolio purposes.
