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

Parsing a restricted set of OpenQASM circuits (≤3 qubits, basic gates), importing them into Lean, and proving equivalence for simple identities (e.g., H;H ≡ I, Euler decompositions, CNOT identities).
