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


