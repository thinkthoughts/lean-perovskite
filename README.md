# lean-perovskite

Using Lean to formalize and test quantitative specifications for perovskite quantum light emission.

## Initial specification

This repository begins with a quantitative specification motivated by Yitong Dong's CU seminar,
*Interface-regulated Perovskite Nanocrystals for Quantum Light Emissions*.

For radiative recombination time `T1` and coherence/dephasing time `T2`, the initial specification is

```text
0 < T2 ≤ 2 T1
```

with normalized coherence

```text
C = T2 / (2 T1).
```

Lean verifies

```text
0 < C ≤ 1
```

and the transform-limit characterization

```text
T2 = 2 T1 ↔ C = 1.
```

## Scientific boundary

The seminar also connects photon indistinguishability with coherence and identifies stochastic
relaxation/time jitter as a limitation on HOM visibility. This repository does **not** identify
measured HOM visibility with `C` without an explicit physical specification supporting that step.

## Next specification

**Which assumptions on stochastic relaxation and timing jitter admit a quantitative bound on HOM visibility?**

This is the next boundary to test against relationships and measurements established by the scientific work.

## Workflow

**Measurements → stated specification → Lean-verified consequence → next specification**

## Build

```text
lake build
```
