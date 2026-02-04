# Quantum Circuit Equivalence CLI Tool

This directory will contain the Python CLI tool for checking quantum circuit equivalences using the Lean prover.

## Planned Structure

```
cli_tool/
├── src/
│   ├── __init__.py
│   ├── main.py           # CLI entry point
│   ├── parser.py         # Circuit notation parser
│   ├── lean_interface.py # Interface with Lean
│   └── utils.py          # Utility functions
├── tests/
│   └── test_*.py         # Unit tests
├── requirements.txt      # Python dependencies
├── setup.py              # Package setup
└── README.md             # This file
```

## Usage (To Be Implemented)

```bash
python -m cli_tool.main "H H" "I"
```

This will verify that applying the Hadamard gate twice is equivalent to the identity.

## Features (Planned)

- Parse circuit notation (e.g., "H X Z", "CNOT", etc.)
- Generate Lean code for circuit equivalence checking
- Execute Lean prover
- Return results in human-readable format
- Support for single-qubit and multi-qubit gates
