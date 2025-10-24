# QAMP 2025 Project #35: Equivalence Checking Between OpenQASM Programs in Lean

## Description

This project aims to bridge formal verification and quantum programming by developing a Lean-based framework for proving equivalence between OpenQASM programs. OpenQASM is the de facto standard language for describing quantum circuits, but current compiler toolchains rely heavily on heuristic optimization and empirical testing rather than formal guarantees. By embedding OpenQASM circuits into Lean, a state-of-the-art theorem prover, we can reason rigorously about whether two programs implement the same quantum operation.

The project will focus on a practical subset of OpenQASM (single-qubit gates, controlled-NOT, sequential/parallel composition, and ancilla qubits). We will define a formal semantics in Lean, implement parsing from OpenQASM into Lean’s intermediate representation, and build tactics to prove circuit equivalence up to global phase and ancilla-assisted equivalence. At the end of three months, we aim to produce a working prototype that can parse two OpenQASM circuits, translate them into Lean, and either produce a formal equivalence proof or a counterexample. This project contributes toward verified quantum compilation and formal guarantees for quantum program correctness.

See original proposal: https://github.com/qiskit-advocate/qamp-2025/issues/35

## Deliverables

### Primary Deliverables:

- [ ] A Lean library defining a formal intermediate representation (IR) of OpenQASM circuits and their denotational semantics.

- [ ] An automated equivalence checker in Lean that proves whether two OpenQASM programs are equivalent up to global phase or ancilla-assisted equivalence.

- [ ] A command-line tool (leanqasm-check) that parses OpenQASM files, feeds them into Lean, and outputs equivalence results or counterexamples.

- [ ] A technical report or blog post documenting methodology, results, and case studies (e.g., verifying compiler optimizations).

### Minimal Viable Product (MVP):

The expected outcome of this project is a **fully functional Quantum Circuit Equivalence Checker built in Lean**, where one could input two OpenQASM 3.0 circuit files—whether they involve one, two, or three qubits—and instantly receive a formal verdict on whether the circuits are equivalent up to a global phase. The tool would provide both **symbolic proofs inside Lean** (for small Clifford+T circuits) and **numerical verification** (for larger, approximate cases), all through a simple command-line interface. The system would show intermediate steps like normalization, rewriting, and canonical decomposition, making it not only a checker but also an **educational and debugging companion** for quantum programmers. If fully realized, this project would mark one of the first end-to-end pipelines bridging **formal verification in Lean** with **quantum circuit semantics**, enabling trustworthy reasoning about real OpenQASM programs.
In the future, it needs to be extended toward **n-qubit generalization** with scalable data structures (e.g., tensor networks or ZX-calculus representations), **integration with Qiskit and OpenQASM simulators**, and **support for approximate or noisy circuits** where unitary equivalence must tolerate physical errors. Long-term, the vision is to evolve it into a **certified quantum compiler verification toolchain**, connecting formal proofs to real hardware-level implementations.


Here’s your **3-month task plan** formatted in clean **GitHub-ready Markdown**, so you can paste it directly into a `README.md` or `PROJECT_PLAN.md` for your Lean quantum circuit equivalence checker project.

---

# 🧠 Quantum Circuit Equivalence Checker — Task Plan (Lean + OpenQASM3)

**Duration:** 12 Weeks (3 Months)

---

## 📅 Weeks 1–4 — Foundations + 1-Qubit Equivalence

### **Week 1**

**Task A – Repo & Lean Scaffold**

* [ ] Set up Lean 4 + mathlib4, create repository with CI (`lakefile`, `.github/workflows`).
* [ ] Define core types:

  ```lean
  def Qubit := Fin 2
  def Ket := Qubit → ℂ
  def Mat (m n : Nat) := Fin m → Fin n → ℂ
  ```
* [ ] Implement helper functions: `Id`, `dagger`, `⊗` (stub).
* [ ] ✅ *Deliverable:* CI passes; proof `dagger (Id 2) = Id 2`.

**Task B – Gate Syntax (1-Qubit)**

* [ ] Define inductive type:

  ```lean
  inductive Gate1
  | I | X | Y | Z | H | S | T | Rz (θ : ℝ)
  ```
* [ ] Define `Circ1 := List Gate1`.
* [ ] Implement pretty-printer and parser stubs.
* [ ] ✅ *Deliverable:* Round-trip printer tests pass.

---

### **Week 2**

**Task A – Semantics for 1-Qubit Gates**

* [ ] Implement `⟦_⟧₁ : Gate1 → Mat 2 2` (exact entries).
* [ ] Define `denote₁ : Circ1 → Mat 2 2`.
* [ ] Prove unitarity lemmas for all base gates.
* [ ] ✅ *Deliverable:* All unitarity proofs compile.

**Task B – Equivalence up to Global Phase**

* [ ] Define `≈φ` on 2×2 matrices:
  `U ≈φ V ↔ ∃λ : ℂ, |λ|=1 ∧ U = λ • V`.
* [ ] Prove reflexive/symmetric/transitive.
* [ ] Implement decision procedure for discrete angle set {k·π/2ᵈ}.
* [ ] ✅ *Deliverable:* Verified examples: `H;H ≈φ I`, `S;S ≈φ Z`, etc.

---

### **Week 3**

**Task A – Canonical/Euler Normalization**

* [ ] Implement ZYZ decomposition for 1-qubit circuits.
* [ ] Define `normalize₁ : Circ1 → (α,β,γ)` with proof of equivalence.
* [ ] ✅ *Deliverable:* Random tests confirm `denote₁ c ≈φ fromZYZ(normalize₁ c)`.

**Task B – 1-Qubit CLI Checker**

* [ ] Implement CLI to read two 1-qubit circuit files.
* [ ] Output: `Equivalent` / `Not Equivalent` (exit code 0/1).
* [ ] ✅ *Deliverable:* 10 golden test cases pass.

---

### **Week 4**

**Task A – Minimal OpenQASM-3 Parser (1-Qubit)**

* [ ] Parse: `qubit[1];`, `x q[0];`, `h q[0];`, `rz(angle) q[0];`.
* [ ] Map to `Circ1`.
* [ ] ✅ *Deliverable:* Round-trip verified on example files.

**Task B – Docs & Benchmarks**

* [ ] Write tutorial (`docs/ONE_QUBIT.md`).
* [ ] Micro-benchmark Lean `#eval` timing.
* [ ] ✅ *Deliverable:* Table of runtime vs circuit length.

---

## ⚛️ Weeks 5–8 — 2-Qubit Extension

### **Week 5**

**Task A – Tensor Product & Lift**

* [ ] Implement `⊗` for matrices, with lemmas `(A⊗B)† = A†⊗B†`.
* [ ] Define lifting of 1-qubit gates to wire 0/1.
* [ ] ✅ *Deliverable:* Verified on `(H on wire0);(H on wire0) ≈φ Id`.

**Task B – 2-Qubit Syntax & Semantics**

* [ ] Define:

  ```lean
  inductive Gate2
  | CNOT | SWAP | CZ | OneQ (wire : Fin 2) (g : Gate1)
  ```
* [ ] Implement `denote₂ : Circ2 → Mat 4 4`.
* [ ] ✅ *Deliverable:* CNOT and SWAP truth-tables verified.

---

### **Week 6**

**Task A – Phase-Equivalence for 4×4**

* [ ] Extend `≈φ` to 4×4 unitaries.
* [ ] Implement symbolic matrix hashing for entries in `{0, ±1, ±1/√2, e^{iπ/4}, …}`.
* [ ] ✅ *Deliverable:* `CNOT;CNOT ≈φ Id`.

**Task B – Local Rewrite System**

* [ ] Implement rewrite rules: commute disjoint gates, cancel inverses, H-X-H = Z, etc.
* [ ] Prove each rule preserves `≈φ`.
* [ ] ✅ *Deliverable:* Rewriting engine passes soundness tests.

---

### **Week 7**

**Task A – Canonical Normal Form (2-Qubit)**

* [ ] Implement lexicographic normalization: push locals inward, sort commuting gates.
* [ ] ✅ *Deliverable:* `normalize₂ (normalize₂ c) = normalize₂ c`.

**Task B – 2-Qubit CLI + QASM Parser**

* [ ] Parse `cx q[0],q[1];`, `cz;`, `swap;`.
* [ ] Extend CLI for automatic arity detection.
* [ ] ✅ *Deliverable:* Bell-state circuits verified equivalent.

---

### **Week 8**

**Task A – Property Tests & Fuzzing**

* [ ] Random circuit generator + equivalence oracle.
* [ ] ✅ *Deliverable:* 1 000 tests, zero mismatches.

**Task B – Performance Optimization**

* [ ] Reduce allocations, reuse buffers for 4×4 ops.
* [ ] ✅ *Deliverable:* ≥2× speedup on depth 100 circuits.

---

## 🧩 Weeks 9–12 — 3-Qubit Stage + Polish

### **Week 9**

**Task A – 3-Qubit Syntax & Semantics**

* [ ] Define `Gate3 := CCX | CCZ | TwoQ g (i,j) | OneQ g k`.
* [ ] Implement `denote₃ : Circ3 → Mat 8 8`.
* [ ] ✅ *Deliverable:* GHZ/Toffoli verification.

**Task B – Wire Permutation System**

* [ ] Add `permute : Circ n → Perm n → Circ n` with correctness proof.
* [ ] ✅ *Deliverable:* SWAP network verified.

---

### **Week 10**

**Task A – 3-Qubit Normalization**

* [ ] Extend rewrite rules to 3-wire circuits.
* [ ] ✅ *Deliverable:* Idempotence & shrinkage proven.

**Task B – 3-Qubit CLI + QASM**

* [ ] Parse `ccx`, `ccz`, `barrier` (ignored).
* [ ] ✅ *Deliverable:* Toffoli equivalence check passes.

---

### **Week 11**

**Task A – Soundness Test Suite**

* [ ] 50 curated identities (KAK-style, control-phase commutation, GHZ variants).
* [ ] ✅ *Deliverable:* All pass.

**Task B – Documentation & Tutorials**

* [ ] Write `README.md`, `docs/TUTORIAL_*.md`.
* [ ] ✅ *Deliverable:* End-to-end user walkthrough.

---

### **Week 12**

**Task A – Packaging & Release**

* [ ] Tag v0.1 release; add `--help` UX polish, changelog, license.
* [ ] ✅ *Deliverable:* Clean install in <10 min.

**Task B – Proof Automation (Stretch)**

* [ ] Create Lean tactics for common matrix/unitarity proofs.
* [ ] ✅ *Deliverable:* ≥20 % proof LOC reduction.

---
