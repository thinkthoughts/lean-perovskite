# lean-perovskite

Using Lean to formalize and test quantitative specifications for
perovskite quantum light emission.

This repository is motivated by Yitong Dong's CU seminar,
*Interface-regulated Perovskite Nanocrystals for Quantum Light
Emissions*.

## Coherence specification

For radiative recombination time `T1` and coherence/dephasing time `T2`,
the first specification is

``` text
0 < T2 ≤ 2 T1
```

with normalized coherence

``` text
C = T2 / (2 T1).
```

Lean verifies

``` text
0 < C ≤ 1
```

and the transform-limit characterization

``` text
T2 = 2 T1 ↔ C = 1.
```

## Stochastic-relaxation specification

The seminar identifies stochastic-relaxation timing jitter as a
limitation on Hong-Ou-Mandel (HOM) photon indistinguishability and
presents the limiting quantity

``` text
L = Γ_relaxation / (Γ_relaxation + Γ_X).
```

For positive rates, Lean verifies

``` text
0 < L < 1.
```

The formalization also verifies the directional constraints of the
stated model:

``` text
Γ_relaxation ↑  →  L ↑
Γ_X ↑           →  L ↓
```

with the other positive rate held fixed.

A measured HOM visibility is represented separately and can be admitted
under the stated relaxation specification by

``` text
0 ≤ V_HOM ≤ L.
```

This keeps the experimental measurement distinct from the Lean-verified
consequences of the stated physical specification.

## Scientific boundary

The coherence ratio

``` text
C = T2 / (2 T1)
```

and the relaxation-limited HOM quantity

``` text
L = Γ_relaxation / (Γ_relaxation + Γ_X)
```

remain separate specifications.

The repository does not infer a quantitative relation between `C` and
measured HOM visibility without an explicit physical model supporting
that relation.

## Next specification

**Which experimentally supported assumptions admit a quantitative
relation among exciton coherence, stochastic-relaxation timing jitter,
and measured HOM visibility?**

This is the next specification to test against relationships and
measurements established by the scientific work.

## Workflow

**Measurements → stated specification → Lean-verified consequence → next
specification**

## Lean verification

The current formalization verifies:

-   positivity and upper bounds for normalized coherence;
-   the transform-limit characterization;
-   positivity and strict upper bounds for the relaxation-limited HOM
    quantity;
-   the HOM visibility consequence under the stated bound;
-   monotonicity with increasing relaxation rate; and
-   antitonicity with increasing `Γ_X`.

## Build

``` text
lake build LeanPerovskite
```

The current formalization builds successfully with the Lean toolchain
and mathlib versions pinned by this repository.
