import Qamp352025.SingleQubitGateDefinitions
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Proof that H · H = I using SingleQubitGateDefinitions

This file proves that applying the Hadamard gate twice yields the identity matrix,
using the gate definitions from SingleQubitGateDefinitions.lean.
-/

open Gate1 Matrix Complex

-- First, let's prove a helper lemma about 1/√2
lemma inv_sqrt_two_squared : (inv_sqrt_2 : ℂ) * inv_sqrt_2 = 1/2 := by
  unfold inv_sqrt_2
  norm_cast
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

-- Another helper: 2 * (1/√2)² = 1
lemma two_inv_sqrt_two_squared : 2 * inv_sqrt_2 * inv_sqrt_2 = 1 := by
  rw [mul_assoc, inv_sqrt_two_squared]
  norm_num


-- Helper for matrix element calculations
lemma hadamard_mul_00 : (H.toMatrix * H.toMatrix) 0 0 = 1 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]
  ring_nf
  rw [← two_inv_sqrt_two_squared]
  ring

lemma hadamard_mul_01 : (H.toMatrix * H.toMatrix) 0 1 = 0 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma hadamard_mul_10 : (H.toMatrix * H.toMatrix) 1 0 = 0 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]


lemma hadamard_mul_11 : (H.toMatrix * H.toMatrix) 1 1 = 1 := by
  unfold toMatrix
  simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]
  ring_nf
  rw [← two_inv_sqrt_two_squared]
  ring

-- Main theorem: H² = I
theorem hadamard_squared_eq_id : H.toMatrix * H.toMatrix = I.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact hadamard_mul_00
  · exact hadamard_mul_01
  · exact hadamard_mul_10
  · exact hadamard_mul_11

-- Alternative formulation using the circuit semantics
theorem hadamard_circuit_squared : Circ1.toMatrix [H, H] = 1 := by
  unfold Circ1.toMatrix
  simp [List.foldl, hadamard_squared_eq_id, identity_gate_matrix]

-- We can also express this as: the circuit [H, H] is equivalent to the empty circuit
theorem hadamard_twice_is_identity : Circ1.toMatrix [H, H] = Circ1.toMatrix [] := by
  rw [hadamard_circuit_squared]
  unfold Circ1.toMatrix
  simp [List.foldl]

#check hadamard_squared_eq_id
#check hadamard_circuit_squared
#check hadamard_twice_is_identity

/-!
## Summary

We've proven three equivalent formulations:
1. `H.toMatrix * H.toMatrix = 1` - Direct matrix multiplication
2. `Circ1.toMatrix [H, H] = 1` - Using circuit semantics
3. `Circ1.toMatrix [H, H] = Circ1.toMatrix []` - Circuit equivalence

The proof works by:
- Computing each element of the product matrix
- Using the fact that (1/√2)² + (1/√2)² = 1/2 + 1/2 = 1
- And that (1/√2)² - (1/√2)² = 0

This demonstrates that the Hadamard gate is self-inverse, a fundamental property
in quantum computing.
-/
