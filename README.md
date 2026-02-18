# matmul-engine

## Production-Grade 32×32 BF16 Systolic Array Accelerator · ASAP7 7nm

[![Flow](https://img.shields.io/badge/Flow-RTL%20to%20GDS-brightgreen)](#)
[![PDK](https://img.shields.io/badge/PDK-ASAP7%207nm-blue)](#)
[![Tools](https://img.shields.io/badge/Tools-Cadence%20Genus%20%2B%20Innovus-orange)](#)
[![Timing](https://img.shields.io/badge/Timing-Met%20%E2%9C%93-success)](#)
[![License](https://img.shields.io/badge/License-Educational-lightgrey)](#license)

---

## What Is This?

A silicon-targeted matrix multiply accelerator — the kind of engine at the core of every TPU, NPU, and AI chip. Designed from scratch in SystemVerilog, hardened for tapeout on ASAP7 7nm FinFET, and validated through Cadence Genus synthesis and Innovus place-and-route.

This isn't a classroom project with a working simulation. It's a production-architecture design with SRAM-backed storage, double-buffered inputs, AXI4 protocol hardening, IEEE 754-aware numerics, and registered activation pipelines — the same concerns you'd face on a real chip team.

**Key numbers (validated INT8 8×8 configuration):**

| Metric | Value |
|--------|-------|
| Frequency | **667 MHz** |
| Peak Throughput | **42.7 GOPS** |
| Efficiency | **3.04 GOPS/mW** |
| Setup WNS | **+21.6 ps** (timing met ✓) |
| Total Power | **14.05 mW** |
| Technology | ASAP7 7nm FinFET |

---

## Architecture

```
                    Weight columns (top edge)
                    ↓        ↓        ↓        ↓
                 col[0]   col[1]   col[2]  col[N-1]
                    |        |        |        |
  row[0]  ────→ [PE00] → [PE01] → [PE02] → [PE0,N-1]
  row[1]  ────→ [PE10] → [PE11] → [PE12] → [PE1,N-1]
    ⋮               ⋮        ⋮        ⋮        ⋮
  row[N-1]────→ [PEN0] → [PEN1] → [PEN2] → [PEN,N-1]

  Activation rows (left edge)

  Each PE: acc[i][j] += weight × activation   (BF16 × BF16 → FP32)
  Output-stationary: results accumulate in-place.
  Inputs staggered by skew controllers for diagonal wavefront.
```

### System Block Diagram

```
┌────────────────────────────────────────────────────────────────────┐
│                            tpu_top                                 │
│                                                                    │
│  ┌─────────────────────┐        ┌─────────────────────────────┐    │
│  │  Reset Synchronizer │        │     tpu_axi4_wrapper        │    │
│  │ (2-stage async→sync)│        │                             │    │
│  └──────────┬──────────┘        │  AXI4 Slave (64-bit burst)  │    │
│             │ rst_n_sync        │  WSTRB · SLVERR · Busy Prot │    │
│             ▼                   │  CTRL · MAT_A/B · RESULT    │    │
│  ┌──────────────────────────────┤  PERF · BIAS                │    │
│  │         systolic_top         └──────────┬──────────────────┘    │
│  │                                         │                       │
│  │  ┌─────────┐ ┌─────────┐                │                       │
│  │  │ SRAM A  │ │ SRAM A' │ ◄── double     │                       │
│  │  │ Bank 0  │ │ Bank 1  │     buffer     │                       │
│  │  └────┬────┘ └────┬────┘                │                       │
│  │       └─────┬─────┘                     │                       │
│  │             ▼                           │                       │
│  │  ┌──────────────────┐                   │                       │
│  │  │ Skew Controller  │──→ col_skewed     │                       │
│  │  └──────────────────┘       │           │                       │
│  │                             ▼           │                       │
│  │  ┌─────────┐ ┌─────────┐ ┌────────────┐ │                       │
│  │  │ SRAM B  │ │ SRAM B' │ │  32×32     │ │                       │
│  │  │ Bank 0  │ │ Bank 1  │ │  Systolic  │ │                       │
│  │  └────┬────┘ └────┬────┘ │  Array     │ │                       │
│  │       └─────┬─────┘      │ (1024 PEs) │ │                       │
│  │             ▼            └─────┬──────┘ │                       │
│  │  ┌──────────────────┐         │         │                       │
│  │  │ Skew Controller  │──→ row  │         │                       │
│  │  └──────────────────┘         ▼         │                       │
│  │                      ┌───────────────┐  │                       │
│  │  ┌──────────────┐    │ Activation    │  │  ◄─ NONE/ReLU/GeLU    │
│  │  │ Bias Reg File│───→│ Units (×32)   │  │                       │
│  │  │  (32×FP32)   │    │ (registered)  │  │                       │
│  │  └──────────────┘    └───────┬───────┘  │                       │
│  │                              ▼          │                       │
│  │  ┌───────────┐       ┌──────────────┐   │                       │
│  │  │    FSM    │─ctrl─→│ Result SRAM  │   │  ◄── drained from PEs │
│  │  │ Controller│       │  (32 rows)   │   │                       │
│  │  └───────────┘       └──────────────┘   │                       │
│  │                                         │                       │
│  │  ┌───────────────────┐                  │                       │
│  │  │  Perf Counters    │ total·compute·idle cycles                │
│  │  └───────────────────┘                  │                       │
│  └─────────────────────────────────────────┘                       │
└────────────────────────────────────────────────────────────────────┘
```

---

## Features

### Compute
- **32×32 output-stationary systolic array** — 1024 processing elements
- **BF16 × BF16 → FP32 MAC** — 2-stage pipelined, round-to-nearest-even (RNE) on accumulator
- **Accumulate mode** — skip accumulator clear for K-dimension tiling (C += A_tile × B_tile)
- **NaN propagation** — canonical quiet NaN (0x7FC00000), no silent corruption
- **Exponent overflow saturation** — clamp to FP32_MAX instead of wrapping to infinity

### Memory
- **SRAM-backed input storage** — replaces 32K flip-flop bits with synthesizable SRAM macros
- **Double-buffered inputs** — CPU loads next tile while array computes current one (~2× throughput)
- **SRAM-backed result storage** — 32-cycle drain phase eliminates massive 32×32 wire fan-in
- **Behavioral SRAM wrapper** — swap `sram_sp.sv` with foundry macro for tapeout

### Activation & Post-Processing
- **Multi-function activation** — NONE (passthrough), ReLU, GeLU selectable via CTRL register
- **Hardcoded 256-entry GeLU LUT** — synthesis-clean (no `$readmemh`), covers x ∈ [−4, +4)
- **Registered activation output** — breaks timing-critical read path for easier closure
- **Per-column FP32 bias addition** — 32-entry bias register file for C = activation(A×B + bias)

### Bus Interface
- **AXI4 slave** — 64-bit data bus, full INCR burst support for RV64 SoC integration
- **WSTRB handling** — byte-lane-aware control register writes
- **SLVERR responses** — invalid region, write-during-busy, read-only violations
- **Busy protection** — hardware rejects `start` while TPU is computing
- **Level-sensitive interrupt** — `irq = irq_en & done`, cleared on next start

### Physical Design Readiness
- **Reset synchronizer** — 2-stage async-to-sync reset release (metastability protection)
- **Clock gating ready** — structured `pe_en` for synthesis tool ICG insertion
- **Scan ready** — no latches, no async feedback loops, no combinational loops
- **Performance counters** — total/compute/idle cycle counts via MMIO

---

## Memory Map

64-bit AXI data bus. Connect `tpu_top` to an RV64 AXI4 master.

| Address | Region | Access | Description |
|---------|--------|--------|-------------|
| `0x0000` | CTRL | R/W | `[7]=bias_en` `[6:4]=act_func` `[3]=irq_en` `[2]=acc_mode` `[1]=done(RO)` `[0]=start(WO,busy-protected)` |
| `0x1000` | MAT_A | W | Weight matrix. Row i at `i×64B`, 8 beats/row (32 BF16 values) |
| `0x2000` | MAT_B | W | Activation matrix. Same layout as MAT_A |
| `0x3000` | RESULT | R | Result matrix. Row i at `i×128B`, 16 beats/row (32 FP32 values) |
| `0x4000` | PERF | R | `+0x0`=total cycles, `+0x8`=compute cycles, `+0x10`=idle cycles |
| `0x5000` | BIAS | W | Per-column FP32 bias. Entry j at `j×8B` |

### CTRL Register Detail

| Bit(s) | Name | R/W | Description |
|--------|------|-----|-------------|
| 0 | start | WO | Pulse triggers computation. Ignored if busy. |
| 1 | busy | RO | High while array is computing |
| 2 | acc_mode | R/W | 1 = accumulate (don't clear accumulators) |
| 3 | irq_en | R/W | 1 = enable interrupt on done |
| 6:4 | act_func | R/W | 000=none, 001=ReLU, 010=GeLU |
| 7 | bias_en | R/W | 1 = add bias before activation |

---

## Computation Timing

For N=32, MAC_LATENCY=2:

| Phase | Cycles | Description |
|-------|--------|-------------|
| CLEAR | 1 | Zero accumulators and flush skew registers (skipped if `acc_mode=1`) |
| LOAD | 32 | Stream N rows/columns through skew controllers into PE array |
| DRAIN | 63 | Propagation delay: last data reaches PE[31][31] and commits |
| DRAIN_RESULT | 32 | Copy PE results through activation units into result SRAM |
| DONE | 1 | Signal completion, assert interrupt if enabled |
| **Total** | **129** | Results readable from SRAM after done pulse |

### Software Tiling Example (K > 32)

```c
// C[M][N] += A[M][K] × B[K][N], tiled along K dimension
for (int kt = 0; kt < K; kt += 32) {
    load_matrix_a(&A[0][kt], 32, 32);   // write to 0x1000
    load_matrix_b(&B[kt][0], 32, 32);   // write to 0x2000
    uint32_t ctrl = START_BIT | (kt > 0 ? ACC_MODE : 0);
    mmio_write(CTRL_ADDR, ctrl);         // start, accumulate if not first tile
    while (mmio_read(CTRL_ADDR) & BUSY_BIT);  // poll busy
}
read_result(&C[0][0], 32, 32);          // read from 0x3000
```

---

## Module Hierarchy

```
tpu_top
├── reset synchronizer (2-stage pipe)
└── tpu_axi4_wrapper              AXI4 slave, MMIO, IRQ, WSTRB, SLVERR
    └── systolic_top              Systolic array datapath
        ├── systolic_controller   FSM: IDLE→CLEAR→LOAD→DRAIN→DRAIN_RESULT→DONE
        ├── sram_sp (×4-6)        Input SRAMs (A×2, B×2 for double buffer)
        ├── input_skew_controller (×2)   Stagger weights and activations
        ├── systolic_array        N×N PE mesh (parameterized)
        │   └── processing_element (×1024)
        │       └── mac_unit      BF16×BF16→FP32, RNE rounding, NaN/overflow
        ├── activation_unit (×32) Registered NONE/ReLU/GeLU with hardcoded LUT
        ├── bias register file    32×FP32
        ├── sram_sp (×1)          Result SRAM (drained from PE array)
        └── performance counters  Total/compute/idle cycle counts
```

---

## File Structure

```
rtl/
├── tpu_top.sv                  Top-level with reset synchronizer
├── tpu_axi4_wrapper.sv         AXI4 slave (WSTRB, SLVERR, busy protection, perf counters)
├── systolic_top.sv             Datapath: SRAMs, skew, array, activation, drain pipeline
├── systolic_controller.sv      FSM with DRAIN_RESULT phase and acc_mode
├── systolic_array.sv           Parameterized N×N PE mesh (was systolic_array_32x32)
├── processing_element.sv       PE: systolic pass-through + MAC
├── mac_unit.sv                 BF16×BF16→FP32 MAC with RNE, NaN, overflow handling
├── input_skew_controller.sv    Channel-k delay-k stagger registers
├── activation_unit.sv          Multi-function activation (NONE/ReLU/GeLU), registered
└── sram_sp.sv                  Behavioral single-port SRAM (swap for foundry macro)

scripts/                        Synthesis and P&R TCL scripts (Cadence flow)
tb/                             Testbenches
PnR/                            Place-and-route outputs
synthesis/                      Genus synthesis outputs
images/                         Layout screenshots and diagrams
```

---

## Validated P&R Results

The INT8 4×4 and 8×8 configurations have been taken through the full Cadence Genus + Innovus RTL-to-GDS flow on ASAP7 7nm. The 32×32 BF16 configuration is the current production RTL — synthesis and P&R for this configuration is in progress.

### 8×8 Array — Post-Route (667 MHz, TT 0.7V 25°C)

| Metric | Value |
|--------|-------|
| Setup WNS | **+21.6 ps** ✓ |
| Hold WNS | Met ✓ |
| Total Power | **14.05 mW** |
| Die Size | 370.4 × 370.4 µm |
| Cell Count | 33,560 |
| Placement Density | 56.6% |

**Power Breakdown:**

| Component | Power (mW) | % |
|-----------|-----------|---|
| Internal | 9.607 | 68.4% |
| Switching | 4.010 | 28.5% |
| Leakage | 0.434 | 3.1% |
| **Total** | **14.050** | |

**Synthesis → P&R Comparison:**

| Metric | Genus | Innovus | Delta |
|--------|-------|---------|-------|
| Setup WNS | 0 ps | +21.6 ps | Improved |
| Cell Count | 31,520 | 33,560 | +6.5% |
| Total Power | 19.91 mW | 14.05 mW | −29.4% |

### 4×4 Array — Post-Route (667 MHz, TT corner)

| Metric | Value |
|--------|-------|
| Setup WNS | **+21 ps** ✓ |
| Hold WNS | **+79 ps** ✓ |
| Total Power | **4.57 mW** |
| Die Size | 192.8 × 192.8 µm |
| Cell Count | 8,228 |

### Scaling Analysis

| Metric | 4×4 | 8×8 | Ratio |
|--------|-----|-----|-------|
| PEs | 16 | 64 | 4.0× |
| Cell Count | 8,228 | 33,560 | 4.08× |
| Die Area | 37,172 µm² | 137,211 µm² | 3.69× |
| Total Power | 4.57 mW | 14.05 mW | 3.07× |
| Peak GOPS | 10.67 | 42.67 | 4.0× |
| GOPS/mW | 2.33 | 3.04 | 1.30× |

Sub-linear power growth with linear throughput scaling — larger arrays are more power-efficient per operation.

---

## Design Decisions

1. **Output-Stationary Dataflow** — Each PE accumulates its own C[i][j] in place. Minimizes result data movement; optimal for weight-reuse inference patterns.

2. **BF16 Inputs / FP32 Accumulator** — BF16 matches FP32's exponent range, making conversion trivial. FP32 accumulator prevents overflow across the full dot-product length.

3. **Round-to-Nearest-Even (RNE)** — Guard-round-sticky bits on the FP32 accumulator. Eliminates the systematic negative bias that truncation-everywhere causes over 32 accumulations.

4. **SRAM over Flip-Flops** — At 7nm, FFs are 8–12× the area of SRAM bitcells. Moving 32K bits of matrix storage to SRAM cuts ~40% of total area.

5. **Double Buffering** — Without it, the AXI bus sits idle for 129 cycles during every computation. With it, the CPU loads the next tile while the array computes, approaching 2× throughput on back-to-back operations.

6. **Result Drain to SRAM** — Instead of exposing 1024 PE outputs as a flat wire array (massive fan-in mux), a 32-cycle drain phase copies results row-by-row through registered activation into SRAM. Cleaner timing, less routing congestion.

7. **Accumulate Mode** — One CTRL bit, one logic gate, but transforms the design from "can only do 32×32" to "can tile arbitrarily large matrices." The highest impact-to-effort ratio change in the design.

8. **Hardcoded GeLU LUT** — `$readmemh` isn't synthesizable for ASIC. A 256-entry `case` statement compiles to a ROM that any synthesis tool can handle.

---

## Roadmap

- [x] INT8 4×4 and 8×8 validated through full RTL-to-GDS (Genus + Innovus, timing met)
- [x] 32×32 BF16 RTL with production hardening (SRAM, double buffer, RNE, AXI hardening)
- [ ] Synthesis and P&R of 32×32 BF16 on ASAP7
- [ ] Cocotb testbench with NumPy golden model (1000+ random matrix regression)
- [ ] SymbiYosys formal verification (AXI protocol, FSM liveness, accumulator reset)
- [ ] INT8 mode (8×8→32-bit integer MAC for quantized inference, 2× throughput)
- [ ] DMA engine with AXI master for autonomous tile fetching
- [ ] Signoff STA with Cadence Tempus (multi-corner multi-mode)
- [ ] Open-source flow: OpenROAD-flow-scripts on ASAP7

---

## Tool Flow

```
  SystemVerilog RTL (.sv)
       │
       ├──→ Verilator / Icarus ──→ Lint + Simulation
       │         │
       │    Cocotb + NumPy ──→ Golden model comparison
       │
       ├──→ SymbiYosys ──→ Formal verification (SVA → SAT solver)
       │
       ▼
  ┌──────────┐  Cadence Genus 23.14
  │ Synthesis│────────────────── ASAP7 LVT + SLVT multi-Vt
  └──────────┘                   Target: 667 MHz+
       │
       ▼
  ┌──────────┐  Cadence Innovus 23.14
  │   P & R  │────────────────── Floorplan → Place → CTS → Route
  └──────────┘                   OCV + SI-aware optimization
       │
       ▼
  DEF + GDSII + SDF
```

---

## Prerequisites

- **Cadence Xcelium** or **Verilator** — RTL simulation
- **Cadence Genus** — Logic synthesis
- **Cadence Innovus** — Place & route
- **ASAP7 7nm PDK** — [GitHub](https://github.com/The-OpenROAD-Project/asap7)
- **Python 3 + NumPy** — Testbench golden model and GeLU LUT generation
- **Cocotb** (optional) — Python-based verification framework

---

## Quick Start

```bash
# 1. Clone
git clone https://github.com/Kev1nLevin/matmul-engine.git
cd matmul-engine

# 2. Simulation (Verilator lint check)
verilator --lint-only -Wall rtl/*.sv

# 3. Synthesis (update ASAP7 paths in scripts/ first)
cd run && genus -f ../scripts/syn_systolic.tcl

# 4. Place & Route
cd PnR/run && innovus -init ../scripts/innovus.tcl
```

---

## License

Released for educational and portfolio purposes.

---

*Built by [Kevin Levin](https://github.com/Kev1nLevin)*
