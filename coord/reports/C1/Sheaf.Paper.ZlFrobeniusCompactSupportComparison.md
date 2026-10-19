## What changed

Proved all six original holes in `Sheaf.Paper.ZlFrobeniusCompactSupportComparison`.
The geometric factorization and composition equalities use `Over.pullback.map_comp`;
properness and open immersion use `MorphismProperty.overPullbackMap`.

Two proved private helpers transport the ringed module adjunction along a scheme
isomorphism and show that its ordinary derived pullback is an equivalence. The
existing forward and inverse mate theorems then prove invertibility of the two
original Frobenius mates. The existing normalized framework open-pullback realization,
applied to the Frobenius automorphism, transports the constructibility property
of the recorded integral pullback to the ordinary completed pullback.

Added six proof-only imports: `Sheaf.Paper.ZlFrameworkOpenExchange`,
`Sheaf.Paper.SfIntegralConstructibleTriangulated`,
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`,
`WeilConjectures.CategoryTheory.InverseMateEquivalence`,
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
Existing public signatures, definitions, public imports and docstrings are retained.
The copied node records the actual argument and dependencies.

## Proved and sorry left

Closed all six original holes, under node
`def-zl-frobenius-compact-support-comparison`:

- `WeilConjectures.zlGeometricCompactification_comm`
- `WeilConjectures.zlGeometricCompactification_isProper`
- `WeilConjectures.zlGeometricCompactification_isOpenImmersion`
- `WeilConjectures.zlFrobeniusMates_isIso`
- `WeilConjectures.zlAmbientFrobenius_constructible`
- `WeilConjectures.zlFiberMap_comp`

Zero holes remain; zero holes added; zero split off. Both private helpers
(`pushforward_of_ringIso_isEquivalence`, `geometricPull_isEquivalence`) are proved.
The proofs use existing recorded library declarations, including declarations
whose own dependencies still contain holes; no new unproved statement is introduced.

## No longer needed

No original import, node or module is pruned. The original node has no proof
steps or proof dependencies; all eight statement dependencies remain necessary for
the geometric, coefficient, constructible and compositor definitions.

No private opposite-category mate argument or new Frobenius reduction tower is
needed: the existing inverse-mate theorem handles the open mate, and the existing
framework realization supplies constructibility transport. The discarded sandbox
route through `Sheaf.Paper.IsomorphismDerivedPullback` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso` needed two additional
coefficient-comparison helpers; neither import nor helper is in the delivery.
`Sheaf.CategoryTheory.MateIsoAlongEquivalences` is also not imported: the upstream
forward theorem gives the equivalence/equivalence specialization directly.
These are discarded exploratory dependencies, not claimed as pruning from the
repository baseline.

## Where the brief, the DAG or earlier work was wrong

The original definition node had an empty proof list despite six supporting theorem
holes. The delivery records the argument explicitly without changing its statement,
its definitions, its source conventions or its unit route.

The retained report was stale: it described helpers absent from the retained Lean
file. The first required dry run found a line break separating an adjunction term
from its dot-notation lemma, and local 10,000-heartbeat caps that prevented coefficient
comparisons from elaborating. Joined the application and removed the artificial caps.
Replaced that longer coefficient-comparison route by the existing framework open
realization. No file timeout or project option was raised. Removed obsolete sandbox
compiled artifacts for two dependencies so compilation uses published dependencies.

Retained searches in `searches.jsonl` cover Lean Finder for invertibility of
adjunction mates along equivalences, Loogle for `CategoryTheory.mateEquiv`, and
library grep for mate and derived-equivalence constructions. Current-source search
found the proved upstream inverse-mate and forward-mate theorems and the normalized
framework open-pullback realization. Their signatures were checked and reused.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
