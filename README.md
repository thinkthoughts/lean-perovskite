# lean-perovskite

Using Lean to formalize and test quantitative specifications for perovskite quantum light emission.

## Initial scope

This repository begins with a quantitative specification motivated by Yitong Dong's CU seminar,
*Interface-regulated Perovskite Nanocrystals for Quantum Light Emissions*.

The initial formalization focuses on the relationship between:

- exciton coherence,
- radiative lifetime, and
- photon indistinguishability.

The goal is to make the stated relationships explicit in Lean and verify what follows from them.

## Workflow

**Measurements → specification → verified consequences → next specifications**

The repository is intended to provide a small, inspectable way to test next specifications against
relationships and measurements already established by the scientific work.

## Build

```text
lake build
```

## Structure

```text
LeanPerovskite/
  Basic.lean
LeanPerovskite.lean
sources/
  README.md
```

`LeanPerovskite/Basic.lean` contains the initial definitions and theorem statements.

`sources/README.md` records the scientific source and the quantitative specification being formalized.
