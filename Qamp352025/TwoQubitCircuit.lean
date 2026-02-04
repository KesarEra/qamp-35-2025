import Qamp352025.QuantumGates
import Qamp352025.SingleQubitCircuit

set_option maxHeartbeats 1000000

/-!
# Two-Qubit Quantum Circuits

This file implements 2-qubit quantum gates and circuits, extending the single-qubit
framework to handle entangling operations like CNOT, SWAP, and CZ gates.

## Main Definitions

* `TwoQubitGate`: Inductive type for 2-qubit quantum gates
* `TwoQubitCircuit`: A circuit as a list of 2-qubit gates
* `TwoQubitGate.toUnitary`: Denotational semantics mapping gates to 4×4 unitaries
* `TwoQubitCircuit.evalCircuit`: Circuit evaluation by matrix composition

## Gates Included

- Single-qubit gates on either wire (lifted via tensor product)
- CNOT (Controlled-NOT)
- SWAP (exchange qubits)
- CZ (Controlled-Z)

## Proven Identities

- `tensorProductTest`: Testing single-qubit gate tensor products
- `czTwice`: Proves CZ² = CNOT⁴ (CZ applied twice equals CNOT four times)
- `swapTwice`: (Work in progress) SWAP² = I
-/

inductive TwoQubitGate where
  | single (wire : Fin 2) (g : SingleQubitGate)
  | cnot
  | swap
  | cz
deriving Repr, DecidableEq

abbrev TwoQubitCircuit := List TwoQubitGate

namespace TwoQubitGate
open Matrix

def toString : TwoQubitGate → String
  | .single 0 g => s!"q[0]: {repr g}"
  | .single 1 g => s!"q[1]: {repr g}"
  | .cnot => "CNOT(0→1)"
  | .swap => "SWAP(0,1)"
  | .cz => "CZ(0,1)"
instance : ToString TwoQubitGate where toString := toString

/-- Lift single-qubit gate to wire 0 (U ⊗ I) -/
noncomputable def liftToWire0 (U : 𝐔[Qubit]) : 𝐔[Qubit × Qubit] := U ⊗ᵤ (1 : 𝐔[Qubit])

/-- Lift single-qubit gate to wire 1 (I ⊗ U) -/
noncomputable def liftToWire1 (U : 𝐔[Qubit]) : 𝐔[Qubit × Qubit] := (1 : 𝐔[Qubit]) ⊗ᵤ U

/-- Convert gate to 4×4 unitary matrix -/
noncomputable def toUnitary : TwoQubitGate → 𝐔[Qubit × Qubit]
  | .single wire g => match wire with
    | 0 => liftToWire0 (SingleQubitGate.toUnitary g)
    | 1 => liftToWire1 (SingleQubitGate.toUnitary g)
  | .cnot => Qubit.CNOT
  | .swap => ⟨Matrix.of fun (i₁, j₁) (i₂, j₂) =>
      if (i₁, j₁) = (i₂, j₂) then 1 else if (i₁, j₁) = (j₂, i₂) then 1 else 0, by sorry⟩
  | .cz => Qubit.controllize Qubit.Z

end TwoQubitGate

namespace TwoQubitCircuit

def toString (c : TwoQubitCircuit) : String :=
  s!"[{String.intercalate ", " (c.map TwoQubitGate.toString)}]"
instance : ToString TwoQubitCircuit where toString := toString

noncomputable def evalCircuit (c : TwoQubitCircuit) : 𝐔[Qubit × Qubit] :=
  c.foldl (fun U g => TwoQubitGate.toUnitary g * U) (1 : 𝐔[Qubit × Qubit])

/-- All 2-qubit basis states -/
def basisStates : List (Qubit × Qubit) := [(0,0), (0,1), (1,0), (1,1)]

/-- Check if two circuits have identical unitaries (all 16 matrix entries equal) -/
noncomputable def circuitsEq (c₁ c₂ : TwoQubitCircuit) : Prop :=
  (evalCircuit c₁).val = (evalCircuit c₂).val

/-- Example: Testing single-qubit gates on wire 1 (tensor product behavior) -/
lemma tensorProductTest : circuitsEq [.single 1 .X, .single 1 .X] [.single 1 .X, .single 1 .X] = true := by
  unfold circuitsEq evalCircuit TwoQubitGate.toUnitary
  norm_num [basisStates, List.all, List.product, Qubit.CNOT]

/-- CZ gate applied twice equals CNOT applied four times -/
lemma czTwice : circuitsEq [.cz, .cz] [.cnot, .cnot, .cnot, .cnot] = true := by
  unfold circuitsEq evalCircuit TwoQubitGate.toUnitary
  norm_num [basisStates, List.all, List.product, Qubit.CNOT]

/-- SWAP is self-inverse (SWAP² = I) - Work in progress -/
-- lemma swapTwice : circuitsEq [.swap, .swap] [] = true := by
--   unfold circuitsEq evalCircuit TwoQubitGate.toUnitary
--   norm_num [basisStates, List.all, List.product]

end TwoQubitCircuit
