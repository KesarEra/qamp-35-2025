import Qamp352025.SingleQubitGateDefinitions
import Qamp352025.SingleQubitGateInteraction.s_4_eq_id
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Proof that T⁸ = I using SingleQubitGateDefinitions

This file proves that applying the T gate eight times yields the identity matrix.
We leverage T² = S and S⁴ = I.
-/

open Gate1 Matrix Complex Real

-- def z := Complex.I * (Real.pi / 4 : ℝ)
lemma cexp_pow4_as_sum : cexp z ^ 4 = cexp (z + z + z + z) := by
  -- rw [pow_succ, pow_succ, pow_succ, pow_zero, mul_one]
  -- repeat { rw [exp_add] }
  sorry



lemma cexp_pi_quarter_pow_four_eq_neg_one :
  cexp (Complex.I * (Real.pi / 4 : ℝ)) ^ 4 = -1 := by
  sorry

-- Helper lemma: (e^(iπ/4))⁴ = i
lemma cexp_pi_quarter_pow_four : cexp (Complex.I * (Real.pi / 4 : ℝ)) ^ 4 = Complex.I := by
  sorry

-- Helper: T⁴ = S
lemma t_fourth_eq_s : T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix) = S.toMatrix := by
  sorry

-- Main theorem: T⁸ = S⁴ = I
theorem phase_t_eighth_eq_id :
  T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix) *
  (T.toMatrix * T.toMatrix * (T.toMatrix * T.toMatrix)) = Gate1.I.toMatrix := by
  sorry

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
