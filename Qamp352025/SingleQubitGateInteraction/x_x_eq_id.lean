import Qamp352025.SingleQubitGateDefinitions
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option trace.Meta.isDefEq true in
set_option trace.Meta.synthInstance true in

/-!
# Proof that X · X = I using SingleQubitGateDefinitions

This file proves that applying the Pauli-X gate (bit-flip) twice yields the identity matrix.
-/

open Gate1 Matrix Complex

-- Helper for matrix element calculations
lemma pauli_x_mul_00 : (X.toMatrix * X.toMatrix) 0 0 = 1 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma pauli_x_mul_01 : (X.toMatrix * X.toMatrix) 0 1 = 0 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma pauli_x_mul_10 : (X.toMatrix * X.toMatrix) 1 0 = 0 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma pauli_x_mul_11 : (X.toMatrix * X.toMatrix) 1 1 = 1 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

-- Main theorem: X² = I
theorem pauli_x_squared_eq_id : X.toMatrix * X.toMatrix = Gate1.I.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact pauli_x_mul_00
  · exact pauli_x_mul_01
  · exact pauli_x_mul_10
  · exact pauli_x_mul_11

-- Alternative formulation using circuit semantics
theorem pauli_x_circuit_squared : Circ1.toMatrix [X, X] = 1 := by
  unfold Circ1.toMatrix
  simp [List.foldl, pauli_x_squared_eq_id, identity_gate_matrix]

-- Circuit equivalence
theorem pauli_x_twice_is_identity : Circ1.toMatrix [X, X] = Circ1.toMatrix [] := by
  rw [pauli_x_circuit_squared]
  unfold Circ1.toMatrix
  simp [List.foldl]

#check pauli_x_squared_eq_id
#check pauli_x_circuit_squared
#check pauli_x_twice_is_identity

/-!
## Summary

We've proven three equivalent formulations:
1. `X.toMatrix * X.toMatrix = I.toMatrix` - Direct matrix multiplication
2. `Circ1.toMatrix [X, X] = 1` - Using circuit semantics
3. `Circ1.toMatrix [X, X] = Circ1.toMatrix []` - Circuit equivalence

The proof works by showing that applying the Pauli-X gate (bit-flip) twice returns to the identity.
X flips |0⟩ ↔ |1⟩, so applying it twice restores the original state.

The X gate matrix is:
  ⎡ 0  1 ⎤
  ⎣ 1  0 ⎦

So X² = I is immediate from matrix multiplication.
-/
