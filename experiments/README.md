# Experiments and Early Work

This folder contains early explorations and experiments conducted during the QAMP 35 project.

## Structure

### Early Attempts (`early_attempts/`)
Initial attempts at defining quantum gates and proving basic properties:

- `h_mul_h_eq_id.lean`: First proof that H² = I using custom matrix definitions
- `h_mul_h_eq_id_with_time_profile.lean`: Performance profiling of the proof
- `CoreTypes.lean`: Early type definitions
- `SingleQubitGateDefinitions.lean`: Initial gate definitions (complex parameterized version)
- `SingleQubitGateInteraction/`: Detailed proofs of gate identities (H², X², Y², Z², S⁴, etc.)

### Two-Qubit Experiments (`two_qubit/`)
Experimental work on 2-qubit quantum circuits:

- `2_qubit_circuit.lean`: Initial 2-qubit gate and circuit implementation
  - Inductive type for 2-qubit gates (single, CNOT, SWAP, CZ)
  - Tensor product lifting for single-qubit gates
  - Circuit evaluation and equivalence checking
  - Example proof: CNOT² = I

**Note**: This code uses the `QuantumInfo` library structure from the `quantum-info-experiment` repository and may need adaptation for the current QAMP project.

## Legacy Code Notice

**The folder `Qamp352025/SingleQubitGateInteraction/`** still exists in the main directory and contains the same gate interaction experiments. It is considered part of these historical experiments and should be archived.

## Superseded By

All these experiments are superseded by the current working code in the main `Qamp352025/` directory, which provides:
- ✨ Cleaner gate definitions using the `𝐔[α]` notation
- ✨ More concise proofs using the `matrix_expand` tactic
- ✨ Better integration with the circuit equivalence checker
- ✨ Self-contained implementations without external dependencies
