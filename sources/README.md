# Sources

## Seminar

Yitong Dong\
**Interface-regulated Perovskite Nanocrystals for Quantum Light
Emissions**\
CU seminar, September 11, 2026.

## Coherence specification

The photographed seminar slides distinguish:

-   `T1`: radiative recombination time;
-   `T2`: coherence/dephasing time;
-   the transform-limit relation `T2 = 2 T1`; and
-   photon indistinguishability as a quantum-light-emission objective.

The Lean formalization uses the coherence constraint

``` text
0 < T2 ≤ 2 T1
```

and verifies consequences for the normalized coherence quantity

``` text
C = T2 / (2 T1).
```

## Stochastic-relaxation specification

The seminar identifies stochastic relaxation and associated timing
jitter as a limitation on Hong-Ou-Mandel (HOM) visibility and presents
the limiting quantity

``` text
L = Γ_relaxation / (Γ_relaxation + Γ_X).
```

The Lean formalization treats this relationship as a stated physical
specification and verifies consequences for positive rates, including

``` text
0 < L < 1
```

and its directional dependence on `Γ_relaxation` and `Γ_X`.

Measured HOM visibility remains a separate quantity and is admitted
under the stated specification by

``` text
0 ≤ V_HOM ≤ L.
```

## Scientific boundary

The current formalization keeps

``` text
C = T2 / (2 T1)
```

and

``` text
L = Γ_relaxation / (Γ_relaxation + Γ_X)
```

as separate specifications.

It does not infer a quantitative relationship between coherence ratio,
timing jitter, and measured HOM visibility without an explicit physical
model supporting that relationship.

## Next source check

Identify the experimentally supported equation and assumptions, if
available, that quantitatively relate:

-   exciton coherence;
-   stochastic-relaxation timing jitter; and
-   measured HOM visibility.

That relation is the next candidate specification for the Lean
formalization.

**measurement → stated physical specification → Lean-verified
consequence → next specification**
