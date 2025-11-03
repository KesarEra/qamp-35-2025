import Qamp352025.SingleQubitGateDefinitions
import Qamp352025.SingleQubitGateInteraction.z_z_eq_id  -- Import the Z gate proof!
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Proof that S⁴ = I using SingleQubitGateDefinitions

This file proves that applying the S gate four times yields the identity matrix.
We leverage the fact that S² = Z and Z² = I from the Z gate proof.
-/

open Gate1 Matrix Complex

-- First helper: S² = Z
lemma s_squared_eq_z : S.toMatrix * S.toMatrix = Z.toMatrix := by
  unfold toMatrix
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num

-- Intermediate theorem: S² equals Z
theorem s_gate_squared : (S.toMatrix * S.toMatrix) = Z.toMatrix :=
  s_squared_eq_z

-- Main theorem: S⁴ = I (using Z² = I)
theorem phase_s_fourth_eq_id :
  S.toMatrix * S.toMatrix * (S.toMatrix * S.toMatrix) = Gate1.I.toMatrix := by
  calc S.toMatrix * S.toMatrix * (S.toMatrix * S.toMatrix)
      = Z.toMatrix * Z.toMatrix := by
        congr 1
        · exact s_squared_eq_z
        · exact s_squared_eq_z
    _ = Gate1.I.toMatrix := pauli_z_squared_eq_id

-- Alternative formulation using circuit semantics
theorem phase_s_circuit_fourth : Circ1.toMatrix [S, S, S, S] = 1 := by
  unfold Circ1.toMatrix
  simp only [List.foldl]
  have h : S.toMatrix * (S.toMatrix * (S.toMatrix * (S.toMatrix * 1))) =
           S.toMatrix * S.toMatrix * (S.toMatrix * S.toMatrix) := by
    simp [Matrix.mul_assoc]
  rw [h, phase_s_fourth_eq_id, identity_gate_matrix]

-- Circuit equivalence
theorem phase_s_fourth_is_identity : Circ1.toMatrix [S, S, S, S] = Circ1.toMatrix [] := by
  rw [phase_s_circuit_fourth]
  unfold Circ1.toMatrix
  simp [List.foldl]

#check s_squared_eq_z
#check s_gate_squared
#check phase_s_fourth_eq_id
#check phase_s_circuit_fourth
#check phase_s_fourth_is_identity

/-!
## Summary

We've proven:
1. `S² = Z` - S squared equals the Z gate
2. `S⁴ = I` - Four applications return to identity
3. `Circ1.toMatrix [S, S, S, S] = 1` - Using circuit semantics
4. `Circ1.toMatrix [S, S, S, S] = Circ1.toMatrix []` - Circuit equivalence

The proof elegantly chains:
- S⁴ = (S²)² = Z² = I

By importing `pauli_z_squared_eq_id` from the Z gate proof,
we avoid duplicating the computation and make the proof more maintainable.
-/
