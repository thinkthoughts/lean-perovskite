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

## Combined indistinguishability specification

A source-supported quantum-dot model combines coherence/dephasing and
stochastic-relaxation timing-jitter effects multiplicatively.

The combined quantity is

``` text
I = C L
```

or explicitly

``` text
I = (T2 / (2 T1))
    (Γ_relaxation / (Γ_relaxation + Γ_X)).
```

The Lean formalization treats this equation as a stated physical model,
rather than as a relation derived from the perovskite measurements.

Under the existing positivity and coherence assumptions, Lean verifies

``` text
0 < I < 1
```

together with the component constraints

``` text
I < C
I ≤ L.
```

Within the stated model, improving coherence alone therefore leaves
indistinguishability constrained by the relaxation/timing-jitter factor,
while improving the relaxation factor alone leaves indistinguishability
constrained by coherence.

## Scientific boundary

The repository distinguishes three levels:

``` text
C = T2 / (2 T1)
```

is the coherence specification;

``` text
L = Γ_relaxation / (Γ_relaxation + Γ_X)
```

is the stochastic-relaxation specification; and

``` text
I = C L
```

is the source-supported combined indistinguishability model.

The combined model is not presented as a consequence derived from Dong's
perovskite measurements. Lean verifies what follows mathematically once
the model and its assumptions are stated.

Source provenance and the boundary between the seminar specifications,
supporting model literature, and Lean-verified consequences are recorded
in `sources/README.md`.

## Next specification

Test source-supported refinements of the combined model against
interface-regulated perovskite measurements.

The repository provides a place to admit candidate next specifications
and check their consequences against relationships and measurements
already represented in the formalization.

## Workflow

**Measurements → stated specification → Lean-verified consequence → next
specification**

## Lean verification

The current formalization verifies:

-   positivity and upper bounds for normalized coherence;
-   the transform-limit characterization;
-   positivity and strict upper bounds for the relaxation-limited HOM
    quantity;
-   the HOM visibility consequence under the stated relaxation bound;
-   monotonicity with increasing relaxation rate;
-   antitonicity with increasing `Γ_X`;
-   positivity and a strict upper bound for combined
    indistinguishability;
-   the strict coherence constraint `I < C`; and
-   the relaxation constraint `I ≤ L`.

## Repository structure

``` text
LeanPerovskite/
    Basic.lean

docs/
    CU_seminar_260911/

sources/
    README.md

LeanPerovskite.lean
README.md
lakefile.toml
lean-toolchain
```

`LeanPerovskite/Basic.lean` contains the formalization.

`docs/CU_seminar_260911/` records the CU seminar that motivated the
initial formalization.

`sources/README.md` records specification provenance and the current
scientific boundary.

## Build

``` text
lake build LeanPerovskite
```

The current formalization builds successfully with the Lean toolchain
and mathlib versions pinned by this repository.
