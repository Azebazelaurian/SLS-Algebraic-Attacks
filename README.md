# SLS-Algebraic-Attacks

Magma implementations and experimental results for algebraic key-recovery attacks on the Shifted Legendre Symbol Problem and higher power-residue variants.

## Overview

This repository contains experimental Magma code investigating algebraic approaches to secret recovery from multiplicative-coset queries.

The implementations include experiments with quadratic, quartic, and octic power-residue functions.

## Requirements

- Magma Computational Algebra System

## Running the Code

Load the Magma script:

```magma
load "SLS-Algebraic-Attacks.m";
```

## Reproducibility

The code includes experimental parameters, algebraic preprocessing, candidate filtering, and recovery procedures.

The algebraic transcript mode uses a random secret to generate statistics directly. Oracle simulation mode computes statistics from individual oracle evaluations.

## License

This project is distributed under the MIT License.
