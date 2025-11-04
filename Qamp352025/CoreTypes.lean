-- CoreTypes.lean
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option trace.Meta.isDefEq true in
set_option trace.Meta.synthInstance true in

open Complex
namespace CoreTypes

-- Basic type aliases
def Qubit := Fin 2
def Ket := Qubit → ℂ
def Mat (m n : Nat) := Fin m → Fin n → ℂ

-- Identity matrix
def Id (n : Nat) : Mat n n :=
  fun i j => if i = j then (1 : ℂ) else 0

-- Conjugate transpose (dagger)
def dagger {m n : Nat} (A : Mat m n) : Mat n m :=
  fun i j => star (A j i)

-- Example lemma
lemma dagger_Id (n : Nat) : dagger (Id n) = Id n := by
  funext i j
  simp [Id, dagger]
  sorry

#check dagger_Id
#eval Id 2 (⟨0, by decide⟩) (⟨0, by decide⟩)  -- should print 1
#eval Id 2 (⟨0, by decide⟩) (⟨1, by decide⟩)  -- should print 0

end CoreTypes
