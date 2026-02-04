import Qamp352025.SingleQubitGateDefinitions
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option trace.Meta.isDefEq true in
set_option trace.Meta.synthInstance true in

/-!
# Proof that Y · Y = I using SingleQubitGateDefinitions

This file proves that applying the Pauli-Y gate (phase+bit flip) twice yields the identity matrix.
-/

open Gate1 Matrix Complex

-- Helper for matrix element calculations
lemma pauli_y_mul_00 : (Y.toMatrix * Y.toMatrix) 0 0 = 1 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma pauli_y_mul_01 : (Y.toMatrix * Y.toMatrix) 0 1 = 0 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma pauli_y_mul_10 : (Y.toMatrix * Y.toMatrix) 1 0 = 0 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma pauli_y_mul_11 : (Y.toMatrix * Y.toMatrix) 1 1 = 1 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

-- Main theorem: Y² = I
theorem pauli_y_squared_eq_id : Y.toMatrix * Y.toMatrix = Gate1.I.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact pauli_y_mul_00
  · exact pauli_y_mul_01
  · exact pauli_y_mul_10
  · exact pauli_y_mul_11

-- Alternative formulation using circuit semantics
theorem pauli_y_circuit_squared : Circ1.toMatrix [Y, Y] = 1 := by
  unfold Circ1.toMatrix
  simp [List.foldl, pauli_y_squared_eq_id, identity_gate_matrix]

-- Circuit equivalence
theorem pauli_y_twice_is_identity : Circ1.toMatrix [Y, Y] = Circ1.toMatrix [] := by
  rw [pauli_y_circuit_squared]
  unfold Circ1.toMatrix
  simp [List.foldl]

#check pauli_y_squared_eq_id
#check pauli_y_circuit_squared
#check pauli_y_twice_is_identity

/-!
## Summary

We've proven three equivalent formulations:
1. `Y.toMatrix * Y.toMatrix = I.toMatrix` - Direct matrix multiplication
2. `Circ1.toMatrix [Y, Y] = 1` - Using circuit semantics
3. `Circ1.toMatrix [Y, Y] = Circ1.toMatrix []` - Circuit equivalence

The proof works by showing that applying the Pauli-Y gate twice returns to the identity.
Y performs both bit-flip and phase-flip: |0⟩ ↔ i|1⟩. Applying it twice restores the original state.

The Y gate matrix is:
  ⎡ 0  -i ⎤
  ⎣ i   0 ⎦

Computing Y²:
  Element (0,0): 0·0 + (-i)·i = -i² = -(-1) = 1
  Element (0,1): 0·(-i) + (-i)·0 = 0
  Element (1,0): i·0 + 0·(-i) = 0
  Element (1,1): i·(-i) + 0·0 = -i² = 1

So Y² = I! The `ring` tactic handles this automatically.
-/
