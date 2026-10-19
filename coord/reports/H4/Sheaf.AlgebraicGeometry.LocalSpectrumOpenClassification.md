## What changed

Proved `AlgebraicGeometry.localSpectrum_open_classification` without changing its
statement. The proof follows all five steps of
`lem-a1-local-spectrum-open-classification`: the closed-point criterion for opens,
minimality of nonmaximal primes in dimension at most one, finiteness of minimal
primes over a Noetherian ring, absence of nontrivial specializations in the open,
and affineness of finite discrete schemes.

Used `IsLocalRing.closedPoint_mem_iff`, `Order.krullDim_le_one_iff`,
`PrimeSpectrum.finite_setOfPred_isMin`, `PrimeSpectrum.le_iff_specializes`,
`t1Space_iff_specializes_imp_eq`, and the finite T1 discreteness and finite discrete
scheme affineness instances. All are proved in Mathlib. Replaced the proof-only
minimal-primes import by `Mathlib.RingTheory.Spectrum.Prime.Noetherian`, which
provides the spectrum formulation and imports the same minimal-primes theorem.
Existing public imports, signatures, definitions, and docstrings are unchanged.

The source argument was checked in Stacks `varieties.tex`, `lemma-affine`
(Tag 09N8), and `schemes.tex`, `lemma-scheme-finite-discrete-affine` (Tag 02O0).
The proof works for the empty open and for dimension-zero local rings without any
additional nonemptiness or domain assumption.

Validation: the item compiled through `lcompile.py` in 2.5 seconds without errors
or warnings.

## Proved and sorry left

Closed the only hole:
`AlgebraicGeometry.localSpectrum_open_classification`
(node `lem-a1-local-spectrum-open-classification`).

One of one original holes proved; zero holes added; zero split off; no sorry left.
All ingredients are Mathlib declarations rather than unproved project theorems.

## No longer needed

Removed the direct proof import
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`; its theorem remains used
through the spectrum finiteness API imported from
`Mathlib.RingTheory.Spectrum.Prime.Noetherian`.

No DAG dependencies, project modules, or unit steps are pruned. The existing
proof plan and `proof_deps` still describe the Lean argument, so no node edit is
needed. No new nodes or change records are needed.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib packages the dimension-chain argument as
`Order.krullDim_le_one_iff` and the finite-singleton topology argument as its
finite T1 discreteness instance; these implement the recorded elementary steps.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
