import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Single-Qubit Gates

This file defines the syntax and semantics of single-qubit quantum gates.

## Main definitions

* `Gate1`: Inductive type representing single-qubit gates
* `Circ1`: A quantum circuit as a list of single-qubit gates
* `Gate1.toMatrix`: Denotational semantics mapping gates to 2×2 unitary matrices

## Gates included

- Identity: I
- Pauli gates: X, Y, Z
- Hadamard: H
- Phase gates: S, T, Sdg, Tdg
- Rotation gates: Rx, Ry, Rz (parameterized by angle θ)
- General phase: P (parameterized by angle θ)

-/

-- Convenient notation for 2×2 complex matrices
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Single-qubit quantum gate -/
inductive Gate1 where
  | I : Gate1                    -- Identity
  | X : Gate1                    -- Pauli-X (NOT gate)
  | Y : Gate1                    -- Pauli-Y
  | Z : Gate1                    -- Pauli-Z
  | H : Gate1                    -- Hadamard
  | S : Gate1                    -- Phase gate (π/2)
  | T : Gate1                    -- T gate (π/4)
  | Sdg : Gate1                  -- S dagger (S†)
  | Tdg : Gate1                  -- T dagger (T†)
  | Rx (θ : ℝ) : Gate1          -- Rotation around X-axis
  | Ry (θ : ℝ) : Gate1          -- Rotation around Y-axis
  | Rz (θ : ℝ) : Gate1          -- Rotation around Z-axis
  | P (φ : ℝ) : Gate1           -- Phase gate (general)

/-- A single-qubit circuit is a list of gates -/
def Circ1 := List Gate1

namespace Gate1

open Complex Matrix Real

-- Helper: imaginary unit
local notation "𝕚" => Complex.I

/-- Convert a single-qubit gate to its matrix representation -/
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

/-- Pretty printing for gates -/
def toString : Gate1 → String
  | I => "I"
  | X => "X"
  | Y => "Y"
  | Z => "Z"
  | H => "H"
  | S => "S"
  | T => "T"
  | Sdg => "Sdg"
  | Tdg => "Tdg"
  | Rx _ => "Rx(θ)"
  | Ry _ => "Ry(θ)"
  | Rz _ => "Rz(θ)"
  | P _ => "P(φ)"

instance : ToString Gate1 where
  toString := Gate1.toString

/-- Check if a gate is a Pauli gate -/
def isPauli : Gate1 → Bool
  | I | X | Y | Z => true
  | _ => false

/-- Check if a gate is a Clifford gate -/
def isClifford : Gate1 → Bool
  | I | X | Y | Z | H | S | Sdg => true
  | _ => false

/-- Check if a gate is parameterized (has a real angle parameter) -/
def isParameterized : Gate1 → Bool
  | Rx _ | Ry _ | Rz _ | P _ => true
  | _ => false

end Gate1

namespace Circ1

/-- Denotational semantics: compose gate matrices in sequence -/
noncomputable def toMatrix (c : Circ1) : Mat2 :=
  c.foldl (fun acc g => g.toMatrix * acc) 1

/-- Pretty print a circuit -/
def toString (c : Circ1) : String :=
  String.intercalate " ; " (c.map Gate1.toString)

instance : ToString Circ1 where
  toString := toString

/-- Empty circuit -/
def empty : Circ1 := []

/-- Append a gate to a circuit -/
def append (c : Circ1) (g : Gate1) : Circ1 :=
  c.concat g

/-- Sequential composition of circuits -/
def compose (c1 c2 : Circ1) : Circ1 :=
  List.append c1 c2

-- Notation for circuit composition
infixr:90 " ⋄ " => compose

end Circ1

/-! ## Examples -/

section Examples

open Gate1

-- Example: Hadamard gate matrix
#check Gate1.H.toMatrix

-- Example: Circuit that implements identity (H ; H)
noncomputable def hadamard_twice : Circ1 := [H, H]

-- Example: Pauli-X rotation by π (should be equivalent to X gate)
noncomputable def rx_pi : Circ1 := [Rx Real.pi]

-- Example: S gate applied twice (should equal Z)
noncomputable def s_twice : Circ1 := [S, S]

-- Example circuit composition
noncomputable def example_circuit : Circ1 := [H] ⋄ [X, Y] ⋄ [H]

-- Note: #eval cannot be used with noncomputable definitions
-- But we can still check types and write proofs about these circuits

end Examples
