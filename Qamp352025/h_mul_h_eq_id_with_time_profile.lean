import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

/-
  Lightweight timing profiler (global)

  `profiler`          – enable the timing profiler
  `profiler.threshold` – minimum time (in ms) to report; 0 = show everything
-/
set_option profiler true
set_option profiler.threshold 0

-- Define 2x2 matrices manually
structure Matrix2x2 (α : Type) where
  a00 : α
  a01 : α
  a10 : α
  a11 : αLightweight timing profiler (per theorem / tactic)

-- Extensionality lemma for Matrix2x2
@[ext]
theorem Matrix2x2.ext {α : Type} {A B : Matrix2x2 α}
  (h00 : A.a00 = B.a00) (h01 : A.a01 = B.a01)
  (h10 : A.a10 = B.a10) (h11 : A.a11 = B.a11) : A = B := by
  cases A
  cases B
  simp_all

-- Define matrix multiplication
def Matrix2x2.mul (A B : Matrix2x2 ℝ) : Matrix2x2 ℝ :=
  { a00 := A.a00 * B.a00 + A.a01 * B.a10,
    a01 := A.a00 * B.a01 + A.a01 * B.a11,
    a10 := A.a10 * B.a00 + A.a11 * B.a10,
    a11 := A.a10 * B.a01 + A.a11 * B.a11 }

-- Define identity matrix
def Matrix2x2.id : Matrix2x2 ℝ :=
  { a00 := 1, a01 := 0, a10 := 0, a11 := 1 }

-- Define Hadamard matrix (marked noncomputable because of sqrt)
noncomputable def H : Matrix2x2 ℝ :=
  let c := 1 / Real.sqrt 2
  { a00 := c, a01 := c, a10 := c, a11 := -c }

-- Helper lemma: (1/√2)² + (1/√2)² = 1
lemma inv_sqrt_two_sum :
  (1 / Real.sqrt 2) * (1 / Real.sqrt 2) + (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 := by
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

-- State and prove the theorem
theorem hadamard_squared : H.mul H = Matrix2x2.id := by
  unfold H Matrix2x2.mul Matrix2x2.id
  ext
  · -- Prove a00: (1/√2)² + (1/√2)² = 1
    exact inv_sqrt_two_sum
  · -- Prove a01: (1/√2)² - (1/√2)² = 0
    ring
  · -- Prove a10: (1/√2)² - (1/√2)² = 0
    ring
  · -- Prove a11: -(1/√2)² + (1/√2)² = 1
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
