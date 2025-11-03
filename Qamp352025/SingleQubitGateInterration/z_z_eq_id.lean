import Qamp352025.SingleQubitGateDefinitions
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Proof that Z · Z = I using SingleQubitGateDefinitions

This file proves that applying the Pauli-Z gate twice yields the identity matrix.
-/

open Gate1 Matrix Complex

-- Helper for matrix element calculations
lemma pauli_z_mul_00 : (Z.toMatrix * Z.toMatrix) 0 0 = 1 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma pauli_z_mul_01 : (Z.toMatrix * Z.toMatrix) 0 1 = 0 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma pauli_z_mul_10 : (Z.toMatrix * Z.toMatrix) 1 0 = 0 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma pauli_z_mul_11 : (Z.toMatrix * Z.toMatrix) 1 1 = 1 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

-- Main theorem: Z² = I
theorem pauli_z_squared_eq_id : Z.toMatrix * Z.toMatrix = Gate1.I.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact pauli_z_mul_00
  · exact pauli_z_mul_01
  · exact pauli_z_mul_10
  · exact pauli_z_mul_11

lemma identity_gate_matrix : Gate1.I.toMatrix = (1 : Mat2) := by
  unfold Gate1.toMatrix
  ext i j
  simp only [Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> rfl

-- Alternative formulation using circuit semantics
theorem pauli_z_circuit_squared : Circ1.toMatrix [Z, Z] = 1 := by
  unfold Circ1.toMatrix
  simp [List.foldl, pauli_z_squared_eq_id, identity_gate_matrix]

-- Circuit equivalence
theorem pauli_z_twice_is_identity : Circ1.toMatrix [Z, Z] = Circ1.toMatrix [] := by
  rw [pauli_z_circuit_squared]
  unfold Circ1.toMatrix
  simp [List.foldl]

#check pauli_z_squared_eq_id
#check pauli_z_circuit_squared
#check pauli_z_twice_is_identity

/-!
## Summary

We've proven three equivalent formulations:
1. `Z.toMatrix * Z.toMatrix = I.toMatrix` - Direct matrix multiplication
2. `Circ1.toMatrix [Z, Z] = 1` - Using circuit semantics
3. `Circ1.toMatrix [Z, Z] = Circ1.toMatrix []` - Circuit equivalence

The proof works by showing that applying the Pauli-Z gate twice returns to the identity.
The Z gate flips the phase of the |1⟩ state: twice flips it back.
This is much simpler than the Hadamard since Z has only real values (1 and -1).
-/
