## What changed

Proved `WeilConjectures.isomorphismTermwiseModuleInverseImage_exact` in
`Sheaf.Paper.IsomorphismDerivedPullback`, with all signatures and definitions unchanged.
The proof imports `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageComparison`.
Its underlying abelian natural isomorphism identifies the termwise transported functor
with ordinary sheaf inverse image after forgetting modules. For a scheme isomorphism
that inverse image is an equivalence. The module forgetful functor reflects finite
limits and colimits; preservation of binary products supplies additivity.
The existing node records this dependency in its first proof step.
Elaboration options are scoped inside the proof body; no instance-removal command remains.
Change record: `coord/changes/C4-isomorphism-termwise-exactness-elaboration.md`.

## Proved and sorry left

Closed 1 of the original 4 holes:
`WeilConjectures.isomorphismTermwiseModuleInverseImage_exact`.
Added 0 holes; split off 0 statements.

The following three original holes remain unchanged, all attached to
`lem-weil-isomorphism-derived-pullback`:

- `WeilConjectures.isomorphismCompletedCoefficientComparison_existsUnique`:
  the canonical completed-ring comparison and its projection normalization.
- `WeilConjectures.isomorphismFiniteDerivedPullback_termwise`:
  the finite comparison and transport of bounded constructibility.
- `WeilConjectures.isomorphismIntegralDerivedPullback_termwise`:
  the normalized integral Roos-cone comparison and uniform constructible completeness.

## No longer needed

None. Existing imports and dependencies remain needed by the three unchanged proof plans.
No new theorem or module was introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement discrepancy found. The resumed compile exposed ambiguous
coefficient-universe inference in the inherited proof; explicitly typed local
abelian sheafification and local-bijection instances resolve it.
The repaired complete module compiled successfully through lcompile.py.
The proof-scoped option variant compiled in 7.6 seconds. The exactness subargument can be proved
using the existing public underlying-abelian comparison, without reconstructing module
transport through the site equivalence. This works also for empty schemes and zero
coefficient rings: the argument uses only categorical equivalence and faithful exact
forgetful functors, with no nonzero or nonempty hypothesis.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
