/-- Minimal imports for QuantumGates - No full Mathlib! --/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Group
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

-- Core types
open scoped Matrix BigOperators

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic

-- Tactic support
open Lean Parser.Tactic Lean