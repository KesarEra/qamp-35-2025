# Two-Qubit Circuit Experiments

This folder contains early experiments with 2-qubit quantum circuits.

## Files

- `2_qubit_circuit.lean`: Initial implementation of 2-qubit gates and circuits
  - Defines `TwoQubitGate` inductive type (single, CNOT, SWAP, CZ)
  - Implements tensor product lifting for single-qubit gates
  - Circuit evaluation and equivalence checking
  - Example: CNOT² = I proof

## Status

This is experimental work that depends on the `QuantumInfo` library structure. It's kept here for reference as we work on integrating 2-qubit functionality into the main project.

## Dependencies

This code uses:
- `QuantumInfo.Finite.Qubit.Basic` - For qubit definitions
- `QuantumInfo.Finite.CPTPMap` - For quantum maps
- `SingleQubitCircuit` - For single-qubit gate integration

Note: These dependencies may need to be adapted for the current QAMP project structure.
