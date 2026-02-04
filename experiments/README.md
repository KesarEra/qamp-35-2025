# Experiments and Early Work

This folder contains early explorations and experiments conducted during the QAMP 35 project.

## Structure

- **early_attempts/**: Initial attempts at defining quantum gates and proving basic properties
  - `h_mul_h_eq_id.lean`: First proof that H² = I using custom matrix definitions
  - `h_mul_h_eq_id_with_time_profile.lean`: Performance profiling of the proof
  - `CoreTypes.lean`: Early type definitions
  - `SingleQubitGateDefinitions.lean`: Initial gate definitions (complex parameterized version)
  - `SingleQubitGateInteraction/`: Detailed proofs of gate identities (H², X², Y², Z², S⁴, etc.)

## Note

**Legacy Code**: The folder `Qamp352025/SingleQubitGateInteraction/` still exists in the main directory and contains the same gate interaction experiments. It should be considered part of the historical experiments and will be archived.

These files are kept for historical reference but are superseded by the current working code in the main `Qamp352025/` directory, which provides:
- Cleaner gate definitions without complex parameterization
- More concise proofs using the `matrix_expand` tactic
- Better integration with the circuit equivalence checker
