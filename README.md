# QAMP 35 2025 - Quantum Circuit Equivalence in Lean

**Project**: Proving quantum circuit equivalences using the Lean 4 theorem prover

**Team Members**: Kesar Era (Kazi Muktadir Ahmed)

**Mentors**: [To be added]

---

## 🎯 Project Overview

This project explores the formal verification of quantum circuit equivalences using Lean 4. We build on the [Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo) library to create tools for automatically checking whether two quantum circuits are equivalent.

## 📁 Repository Structure

```
qamp-35-2025/
├── Qamp352025/                    # 🔥 MAIN WORKING CODE
│   ├── QuantumGates.lean          # Core quantum gate definitions (H, X, Y, Z, S, T, CNOT)
│   └── SingleQubitCircuit.lean    # Circuit representation and equivalence checking
│
├── cli_tool/                      # 🚀 Python CLI Tool (In Progress)
│   └── README.md                  # CLI tool documentation
│
├── experiments/                   # 📚 Historical experiments
│   └── early_attempts/            # Initial explorations
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

2. **`Qamp352025/SingleQubitCircuit.lean`** - Circuit equivalence checking
   - Defines `SingleQubitGate` inductive type
   - Implements `SingleQubitCircuit` as a list of gates
   - Provides `evalCircuit` to compute unitary matrices
   - Includes `circuitsEqBool` for equivalence checking
   - Contains example proofs (e.g., `H H = I`, `S S = Z`)

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
```

## 📖 Usage Examples

### Proving Circuit Equivalences

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

### Using Quantum Gates Directly

```lean
import Qamp352025.QuantumGates

-- Access gate definitions
def myGate : 𝐔[Qubit] := Qubit.H

-- Use proven identities
example : Qubit.H * Qubit.H = 1 := Qubit.H_sq
example : Qubit.X * Qubit.X = 1 := Qubit.X_sq
```

## 🎓 Key Features

### Gate Definitions
- **Single-qubit gates**: H (Hadamard), X, Y, Z (Pauli), S, T (phase gates)
- **Two-qubit gates**: CNOT, controllize
- **Tensor products**: Compose gates on multiple qubits

### Proven Identities
- `H² = I`, `X² = I`, `Y² = I`, `Z² = I`
- `S² = Z`, `T² = S`
- Anti-commutation: `XY = -YX`, `YZ = -ZY`, `ZX = -XZ`
- Hadamard conjugations: `HXH = Z`, `HZH = X`

### Circuit Equivalence
- Boolean decision procedure for single-qubit circuit equivalence
- Supports arbitrary compositions of gates
- Verified through Lean's type system

## 🔧 Development

### Project Goals
1. ✅ Define core quantum gates in Lean
2. ✅ Implement circuit representation
3. ✅ Create equivalence checking mechanism
4. 🚧 Build Python CLI tool for user-friendly access
5. ⏳ Extend to multi-qubit circuits
6. ⏳ Optimize proof automation

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
