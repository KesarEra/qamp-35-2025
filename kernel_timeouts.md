# Lean Kernel Limitations: 2-Qubit Circuit Equivalence Checker

## Core Finding

**Primary blocker**: Lean-QuantumInfo's generic `controllize` + tensor product definitions cause **exponential kernel normalization cost** when verifying 4×4 unitary matrix equality.

## Timeout Anatomy (1.4M heartbeats)

```
circuitsEqBool c₁ c₂ =
  2 × evalCircuit normalization (~1M heartbeats)
+ 16 × decide(ℂ equality)     (~400k heartbeats)
--------------------------------------------
  TOTAL: TIMEOUT @ default 200k limit
```

## CNOT Unfolding Cascade
```
TwoQubitGate.toUnitary .cnot
  ↓ Qubit.CNOT (Lean-QuantumInfo)
  ↓ controllize Qubit.X
  ↓ Matrix.control (1 ⊗ X)
  ↓ 16×16×16 pattern matches + Real ops
  ↓ 500k+ heartbeats PER CIRCUIT
```

## Scaling Breakdown
| Circuit Type | Matrix Size | Entries | Heartbeats | Status |
|--------------|-------------|---------|------------|--------|
| Single-qubit | 2×2        | 4 ℂ     | ~200k ✓   | Works  |
| 2-qubit CNOT | 4×4        | 16 ℂ    | ~1.4M ✗   | Timeout|

## Workarounds Tested
- `maxHeartbeats 1000000`: Barely passes compilation
- `norm_num [Qubit.CNOT]`: Manual basis enumeration only
- `simp [controllize]`: Still unfolds fully

## Root Cause
Lean-QuantumInfo's **proof-carrying abstractions** (`𝐔[α]`, `controllize`, `⊗ᵤ`):
✅ Beautiful for theorem proving
❌ Deadly for computational decidability

## Recommendation
1. **Manual 4×4 matrices** for decidable checker (bypass abstractions)
2. **Prop-based equivalence** (`∀ ρ, Φ₁ ρ = Φ₂ ρ`) for proofs
3. **External verifier** (SymPy/Z3) + Lean import

**Status**: Proofs scale, computation doesn't. Hybrid approach needed.

## QAMP Context
[QAMP-35-2025] Cross-posted from quantum-info-experiment analysis.