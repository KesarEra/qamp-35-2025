import Qamp352025.SingleQubitGateDefinitions
import Qamp352025.SingleQubitGateInteraction.z_z_eq_id
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option trace.Meta.isDefEq true in
set_option trace.Meta.synthInstance true in

/-!
# Proof that Sdg⁴ = I using SingleQubitGateDefinitions

This file proves that applying the S-dagger gate four times yields the identity matrix.
S-dagger is the inverse (conjugate transpose) of the S gate.
We leverage the fact that Sdg² = Z and Z² = I.
-/

open Gate1 Matrix Complex

-- First helper: Sdg² = Z
lemma sdg_squared_eq_z : Sdg.toMatrix * Sdg.toMatrix = Z.toMatrix := by
  unfold toMatrix
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num

-- Main theorem: Sdg⁴ = I (using Z² = I)
theorem phase_sdg_fourth_eq_id :
  Sdg.toMatrix * Sdg.toMatrix * (Sdg.toMatrix * Sdg.toMatrix) = Gate1.I.toMatrix := by
  calc Sdg.toMatrix * Sdg.toMatrix * (Sdg.toMatrix * Sdg.toMatrix)
      = Z.toMatrix * Z.toMatrix := by
        congr 1
        · exact sdg_squared_eq_z
        · exact sdg_squared_eq_z
    _ = Gate1.I.toMatrix := pauli_z_squared_eq_id

-- Circuit formulation
theorem phase_sdg_circuit_fourth : Circ1.toMatrix [Sdg, Sdg, Sdg, Sdg] = 1 := by
  unfold Circ1.toMatrix
  simp only [List.foldl]
  have h : Sdg.toMatrix * (Sdg.toMatrix * (Sdg.toMatrix * (Sdg.toMatrix * 1))) =
           Sdg.toMatrix * Sdg.toMatrix * (Sdg.toMatrix * Sdg.toMatrix) := by
    simp [Matrix.mul_assoc]
  rw [h, phase_sdg_fourth_eq_id, identity_gate_matrix]

#check sdg_squared_eq_z
#check phase_sdg_fourth_eq_id
#check phase_sdg_circuit_fourth
