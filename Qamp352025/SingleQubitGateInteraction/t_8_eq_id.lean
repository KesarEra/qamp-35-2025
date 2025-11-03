import Qamp352025.SingleQubitGateDefinitions
import Qamp352025.SingleQubitGateInteraction.s_4_eq_id
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Proof that T⁸ = I using SingleQubitGateDefinitions

This file proves that applying the T gate eight times yields the identity matrix.
We leverage T⁴ = S and S⁴ = I.
-/

open Gate1 Matrix Complex

-- Helper lemma: (e^(iπ/4))⁴ = i
lemma cexp_pi_quarter_pow_four : cexp (Complex.I * (Real.pi / 4 : ℝ)) ^ 4 = Complex.I := by
  norm_num [Complex.exp_eq_exp_iff_eq_eq_add_int_mul_two_pi]
  ring

-- Helper: T⁴ = S
lemma t_fourth_eq_s : T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix) = S.toMatrix := by
  unfold toMatrix
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · simp [mul_comm, mul_assoc]
  · simp [mul_comm, mul_assoc]
  · simp [mul_comm, mul_assoc]
  · simp [mul_comm, mul_assoc, cexp_pi_quarter_pow_four]

-- Main theorem: T⁸ = S⁴ = I
theorem phase_t_eighth_eq_id :
  T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix) *
  (T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix)) = Gate1.I.toMatrix := by
  have h1 : T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix) = S.toMatrix := t_fourth_eq_s
  have h2 : T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix) = S.toMatrix := t_fourth_eq_s
  calc T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix) *
       (T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix))
      = S.toMatrix * S.toMatrix := by rw [h1, h2]
    _ = S.toMatrix * S.toMatrix * (S.toMatrix * S.toMatrix) := by ring
    _ = Gate1.I.toMatrix := phase_s_fourth_eq_id

-- Circuit formulation
theorem phase_t_circuit_eighth : Circ1.toMatrix [T, T, T, T, T, T, T, T] = 1 := by
  unfold Circ1.toMatrix
  simp only [List.foldl]
  have h : T.toMatrix * (T.toMatrix * (T.toMatrix * (T.toMatrix *
           (T.toMatrix * (T.toMatrix * (T.toMatrix *
           (T.toMatrix * 1))))))) =
           T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix) *
           (T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix)) := by
    simp [Matrix.mul_assoc]
  rw [h, phase_t_eighth_eq_id, identity_gate_matrix]

#check t_fourth_eq_s
#check phase_t_eighth_eq_id
#check phase_t_circuit_eighth
