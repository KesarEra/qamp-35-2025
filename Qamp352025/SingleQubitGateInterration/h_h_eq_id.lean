import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Single-Qubit Gate Proofs

This file contains proofs about single-qubit quantum gates.

## Main theorems

* `hadamard_involution`: Proves that H ; H = I (Hadamard is self-inverse)
* Helper lemmas for matrix arithmetic with complex numbers

-/

-- Redefine the types and functions from Gate1.lean
-- (In a real project, you would import Gate1.lean instead)

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

inductive Gate1 where
  | I : Gate1
  | X : Gate1
  | Y : Gate1
  | Z : Gate1
  | H : Gate1
  | S : Gate1
  | T : Gate1
  | Sdg : Gate1
  | Tdg : Gate1
  | Rx (θ : ℝ) : Gate1
  | Ry (θ : ℝ) : Gate1
  | Rz (θ : ℝ) : Gate1
  | P (φ : ℝ) : Gate1

def Circ1 := List Gate1

namespace Gate1

open Complex Matrix Real

local notation "𝕚" => Complex.I

noncomputable def toMatrix : Gate1 → Mat2
  | I => Matrix.of ![![1, 0],
                      ![0, 1]]
  | X => Matrix.of ![![0, 1],
                      ![1, 0]]
  | Y => Matrix.of ![![0, -𝕚],
                      ![𝕚, 0]]
  | Z => Matrix.of ![![1, 0],
                      ![0, -1]]
  | H => let s := 1 / Real.sqrt 2
         Matrix.of ![![s, s],
                      ![s, -s]]
  | S => Matrix.of ![![1, 0],
                      ![0, 𝕚]]
  | T => let t := Complex.exp (𝕚 * π / 4)
         Matrix.of ![![1, 0],
                      ![0, t]]
  | Sdg => Matrix.of ![![1, 0],
                        ![0, -𝕚]]
  | Tdg => let t := Complex.exp (-𝕚 * π / 4)
           Matrix.of ![![1, 0],
                        ![0, t]]
  | Rx θ => let c := Real.cos (θ / 2)
            let s := Real.sin (θ / 2)
            Matrix.of ![![c, -𝕚 * s],
                        ![-𝕚 * s, c]]
  | Ry θ => let c := Real.cos (θ / 2)
            let s := Real.sin (θ / 2)
            Matrix.of ![![c, -s],
                        ![s, c]]
  | Rz θ => let e_neg := Complex.exp (-𝕚 * (θ / 2))
            let e_pos := Complex.exp (𝕚 * (θ / 2))
            Matrix.of ![![e_neg, 0],
                        ![0, e_pos]]
  | P φ => Matrix.of ![![1, 0],
                        ![0, Complex.exp (𝕚 * φ)]]

end Gate1

namespace Circ1

noncomputable def toMatrix (c : List Gate1) : Mat2 :=
  c.foldl (fun acc g => g.toMatrix * acc) 1

end Circ1

/-! ## Helper Lemmas -/

namespace Gate1

open Complex Matrix Real

local notation "𝕚" => Complex.I

-- Helper: Identity matrix
noncomputable def identityMatrix : Mat2 :=
  Matrix.of ![![1, 0],
              ![0, 1]]

-- Helper lemma: (1/√2)² + (1/√2)² = 1 (for Complex)
lemma inv_sqrt_two_sum_complex :
  let s : ℂ := (1 / Real.sqrt 2 : ℝ)
  s * s + s * s = 1 := by
  simp only [ofReal_div, ofReal_one]
  have h : Real.sqrt 2 ≠ 0 := by
    apply Real.sqrt_ne_zero'
    norm_num
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp [h]
  field_simp [h2]
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

-- Helper lemma: (1/√2)² - (1/√2)² = 0 (for Complex)
lemma inv_sqrt_two_cancel_complex :
  let s : ℂ := (1 / Real.sqrt 2 : ℝ)
  s * s - s * s = 0 := by
  ring

/-! ## Main Theorem: Hadamard Involution -/

/--
Hadamard gate is self-inverse: H * H = I
This proves that applying the Hadamard gate twice returns to the identity.
-/
theorem hadamard_matrix_squared : H.toMatrix * H.toMatrix = identityMatrix := by
  unfold toMatrix identityMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
    norm_num
    ring_nf
    }
  · -- Case (0, 0): top-left
    convert inv_sqrt_two_sum_complex using 1
    ring
  · -- Case (0, 1): top-right
    convert inv_sqrt_two_cancel_complex using 1
    ring
  · -- Case (1, 0): bottom-left
    convert inv_sqrt_two_cancel_complex using 1
    ring
  · -- Case (1, 1): bottom-right
    have h : Real.sqrt 2 ≠ 0 := by
      apply Real.sqrt_ne_zero'
      norm_num
    have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by simp [h]
    field_simp [h2]
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num

end Gate1

/-! ## Circuit-Level Proofs -/

namespace Circ1

open Gate1

/--
Hadamard circuit involution: The circuit [H, H] equals the identity.
This is the circuit-level version of the matrix theorem.
-/
theorem hadamard_circuit_involution :
  Circ1.toMatrix [Gate1.H, Gate1.H] = Gate1.identityMatrix := by
  unfold Circ1.toMatrix
  simp [List.foldl]
  rw [Matrix.mul_one]
  exact hadamard_matrix_squared

/--
Alternative formulation: H composed with H equals identity gate
-/
theorem hadamard_self_inverse :
  Circ1.toMatrix [Gate1.H, Gate1.H] = Gate1.I.toMatrix := by
  rw [hadamard_circuit_involution]
  rfl

end Circ1

/-! ## Additional Examples and Tests -/

section Examples

open Gate1

-- Verify the theorem type-checks
#check Circ1.hadamard_circuit_involution
#check Circ1.hadamard_self_inverse
#check Gate1.hadamard_matrix_squared

-- Example: We can now use these theorems in other proofs
example : Circ1.toMatrix [H, H, H, H] = Gate1.identityMatrix := by
  unfold Circ1.toMatrix
  simp [List.foldl]
  rw [Matrix.mul_one]
  -- (H * H) * (H * H) = I * I = I
  rw [hadamard_matrix_squared, hadamard_matrix_squared]
  simp [identityMatrix, Matrix.mul_one]

end Examples

/-!
## Proof Summary

We proved that H * H = I at two levels:

1. **Matrix level** (`hadamard_matrix_squared`):
   Proves that the matrix representation of H multiplied by itself equals the identity matrix.

2. **Circuit level** (`hadamard_circuit_involution`):
   Proves that the circuit [H, H] has the same denotation as the identity.

The proof works by:
- Expanding the matrix definitions
- Using extensionality (`ext`) to prove equality entry-by-entry
- Using `fin_cases` to handle each of the 4 matrix entries (2×2)
- Applying algebraic simplification with helper lemmas about 1/√2

This establishes that Hadamard is a self-inverse gate, a fundamental property
used in many quantum algorithms.
-/
