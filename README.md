# QAMP 35 2025 - Quantum Circuit Equivalence in Lean

**Project**: Proving quantum circuit equivalences using the Lean 4 theorem prover

**Team Members**: Kesar Era (Kazi Muktadir Ahmed)

**Mentors**: Omar Shehab

---

## 🎯 Project Overview

This project explores the formal verification of quantum circuit equivalences using Lean 4. We build on the [Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo) library to create tools for automatically checking whether two quantum circuits are equivalent.

## 📁 Repository Structure

```
qamp-35-2025/
├── Qamp352025/                    # 🔥 MAIN WORKING CODE
│   ├── QuantumGates.lean          # Core quantum gate definitions
│   ├── SingleQubitCircuit.lean    # Single-qubit circuit equivalence
│   └── TwoQubitCircuit.lean       # ⭐ Two-qubit circuits (MILESTONE)
│
├── cli_tool/                      # 🚀 Python CLI Tool (In Progress)
│   └── README.md                  # CLI tool documentation
│
├── experiments/                   # 📚 Historical experiments
│   ├── early_attempts/            # Initial single-qubit explorations
│   └── two_qubit/                 # Early 2-qubit experiments
│
├── lakefile.toml                  # Lean build configuration
├── lean-toolchain                 # Lean version specification
└── README.md                      # This file
```

## 🔥 Current Working Code

### Core Files:

1. **`Qamp352025/QuantumGates.lean`** - The foundation
   - Defines the `𝐔[α]` notation for unitary groups
   - Implements basic quantum gates: H, X, Y, Z, S, T
   - Provides CNOT and controllize for two-qubit gates
   - Includes tensor product notation `⊗ᵤ`
   - Contains proven gate identities (H², X², Y², etc.)

2. **`Qamp352025/SingleQubitCircuit.lean`** - Single-qubit circuit equivalence
   - Defines `SingleQubitGate` inductive type
   - Implements `SingleQubitCircuit` as a list of gates
   - Provides `evalCircuit` to compute unitary matrices
   - Includes `circuitsEqBool` for equivalence checking
   - Contains example proofs (e.g., `H H = I`, `S S = Z`)

3. **`Qamp352025/TwoQubitCircuit.lean`** - ⭐ Two-qubit circuits (MILESTONE)
   - Defines `TwoQubitGate` inductive type (single wire gates, CNOT, SWAP, CZ)
   - Implements tensor product lifting for single-qubit gates
   - Provides 4×4 unitary matrix evaluation
   - Includes circuit equivalence checking

## 🚀 Quick Start

### Prerequisites
- Lean 4 (v4.16.0-rc1 or compatible)
- Lake build tool
- Git

### Installation

```bash
git clone https://github.com/KesarEra/qamp-35-2025.git
cd qamp-35-2025
lake build
```

### Running Examples

```bash
# Build the project
lake build Qamp352025

# Check specific proofs
lake build Qamp352025.SingleQubitCircuit
lake build Qamp352025.TwoQubitCircuit
```

## 📖 Usage Examples

### Single-Qubit Circuit Equivalences

```lean
import Qamp352025.SingleQubitCircuit

-- Prove that H H = I
lemma hh_id_eq: circuitsEqBool [.H, .H] [] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp

-- Prove that S S = Z
lemma ss_z_eq : circuitsEqBool [.S, .S] [.Z] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp [Qubit.S_sq]
```

### Two-Qubit Circuits

```lean
import Qamp352025.TwoQubitCircuit

-- CZ applied twice equals CNOT applied four times
lemma czTwice : circuitsEq [.cz, .cz] [.cnot, .cnot, .cnot, .cnot] = true := by
  unfold circuitsEq evalCircuit TwoQubitGate.toUnitary
  norm_num [basisStates, List.all, List.product, Qubit.CNOT]

-- Apply X gate on wire 1 (using tensor product)
example : TwoQubitGate := .single 1 .X
```

### Using Quantum Gates Directly

```lean
import Qamp352025.QuantumGates

-- Access gate definitions
def myGate : 𝐔[Qubit] := Qubit.H

-- Use proven identities
example : Qubit.H * Qubit.H = 1 := Qubit.H_sq
example : Qubit.X * Qubit.X = 1 := Qubit.X_sq

-- Tensor product of gates
example : 𝐔[Qubit × Qubit] := Qubit.X ⊗ᵤ Qubit.H
```

## 🎓 Key Features

### Gate Definitions
- **Single-qubit gates**: H (Hadamard), X, Y, Z (Pauli), S, T (phase gates)
- **Two-qubit gates**: CNOT, SWAP, CZ, controllize
- **Tensor products**: Compose gates on multiple qubits (`⊗ᵤ`)
- **Wire-specific application**: Apply single-qubit gates to specific wires

### Proven Identities

**Single-Qubit:**
- `H² = I`, `X² = I`, `Y² = I`, `Z² = I`
- `S² = Z`, `T² = S`
- Anti-commutation: `XY = -YX`, `YZ = -ZY`, `ZX = -XZ`
- Hadamard conjugations: `HXH = Z`, `HZH = X`

**Two-Qubit:**
- `CZ² = CNOT⁴` (CZ gate self-interaction)
- Tensor product behavior verified
- SWAP² = I (in progress)

### Circuit Equivalence
- Boolean decision procedure for circuit equivalence
- Supports arbitrary compositions of gates
- Works for both single and two-qubit circuits
- Verified through Lean's type system

## 🔧 Development

### Project Goals
1. ✅ Define core quantum gates in Lean
2. ✅ Implement single-qubit circuit representation
3. ✅ Create equivalence checking mechanism
4. ✅ Extend to two-qubit circuits with entangling gates
5. 🚧 Build Python CLI tool for user-friendly access
6. ⏳ Optimize proof automation
7. ⏳ Scale to n-qubit circuits

### Contributing
This is an academic project. If you'd like to contribute or have questions:
- Open an issue
- Submit a pull request
- Contact: kazisujoy@gmail.com

## 📚 References

- [Lean 4 Documentation](https://lean-lang.org/)
- [Lean-QuantumInfo Library](https://github.com/Timeroot/Lean-QuantumInfo)
- [QAMP Program](https://qosf.org/qamp/)

## 📝 License

Copyright (c) 2025 QAMP 35 Team. All rights reserved.

Core quantum gate definitions adapted from Lean-QuantumInfo (MIT License, Copyright © 2025 Alex Meiburg).

---

**Status**: 🚧 Active Development | **Last Updated**: February 2026
