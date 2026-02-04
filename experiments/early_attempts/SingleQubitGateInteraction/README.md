# Single Qubit Gate Interaction Experiments

This folder contains early proofs of basic quantum gate identities using the old `SingleQubitGateDefinitions.lean` framework.

## Files

- `h_h_eq_id.lean` - Proof that H² = I (Hadamard is self-inverse)
- `x_x_eq_id.lean` - Proof that X² = I (Pauli-X is self-inverse)
- `y_y_eq_id.lean` - Proof that Y² = I (Pauli-Y is self-inverse)
- `z_z_eq_id.lean` - Proof that Z² = I (Pauli-Z is self-inverse)
- `s_4_eq_id.lean` - Proof that S⁴ = I (S gate order 4)
- `sdg_4_eq_id.lean` - Proof that S†⁴ = I (S-dagger order 4)

These experiments were superseded by the more concise approach in `Qamp352025/SingleQubitCircuit.lean`.
