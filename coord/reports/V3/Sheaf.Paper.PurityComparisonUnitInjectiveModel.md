## What changed

Proved `AlgebraicGeometry.ProEtale.comparisonUnitInjectiveModel` with exactly its
original signature. The specified finite-coefficient derived adjunction is
`Adjunction.derivedPlus`, so the already proved `derivedPlus_unit_app_fac` theorem
computes its unit. Postcompose with the derived image of the homotopy class of `j`,
apply naturality of `rightDerivedFunctorPlusUnit`, and combine functoriality with
associativity. Localization of `hj` and the injective-complex comparison instance
prove the two isomorphism clauses.

Updated the existing node's proof, proof dependencies and proof origin to this
shorter route, and its declaration docstring to the actual proof. Removed eight
unused imports. The public import change is recorded in
`coord/changes/V3-comparison-unit-injective-model-imports.md`, including every
transitive consumer. Rechecked the downstream scan against the current sources and
added the new regular-immersion consumers and library roots to the record.
The resumed check found 177 downstream modules and added
`Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` to that record. The retained
proof compiled cleanly against the current published build in 46.8 seconds.
The two direct consumers import the removed public modules
explicitly already; no consumer adaptation or signature change is required.

The searches actually run were LeanFinder for the derived-unit resolution
representative, Loogle for `CategoryTheory.Adjunction.derivedPlus_unit_app_fac`,
and grep for the derived comparison and unit formula. LeanFinder returned the
Mathlib derived-unit formulas; Loogle did not index the project-specific lemma;
reading the project source found that lemma in `RightDerivedFunctor.PlusAdjunction`.
The search log is `searches.jsonl`.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.ProEtale.comparisonUnitInjectiveModel`
(node `lem-pur-comparison-unit-injective-model`). Added 0 holes and 0 split-offs.
There are no remaining `sorry` declarations in this delivery.

The theorem signature was compared verbatim against the original and is unchanged.
The final source has zero `sorry` tokens and all lines are at most 100 characters.
The required compiler and server preflight both passed in the delivery dry run;
no axiom beyond the permitted basis was reported.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.

The exactness, coefficient categories and specified adjunction remain available
through `ProEtaleSiteComparisonDerived` and `ProEtaleFiniteModules`, which the
statement needs. No compact-support comparison theorem or independent ringed
pullback theorem is used.

Removed direct proof dependencies:

- `lem-sc-bounded-below-injective-resolution`: the resolution `j` is supplied.
- `lem-sf-comparison-pullback-exact`: exactness instances for the actual comparison
  functor are already supplied with its definition.
- `lem-sp-grothendieck-enough-injectives`: the coefficient adjunction interface
  already transports enough injectives through its specified equivalence.
- `lem-weil-pbc-bounded-below-injectives-kinjective`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`.
- `lem-weil-pbc-termwise-adjunction-homotopy`.
- `prop-pur-kinjective-resolutions-exist`.

The final five dependencies above are unnecessary because the normalized bounded
below derived adjunction is already constructed and proved. Its formula is the
existing Lean-closed node `lem-trf-bounded-below-derived-adjunction`; no new node is
introduced. Retained `lem-weil-pbc-right-derived-plus-injective` for the comparison
and its invertibility. Retained `thm-weil-pbc-site-comparison` only to specify which
canonical adjunction is meant, as before; its compact-support realization is unused.
Withdrew obsolete top-level tool approvals for
`lem-weil-pbc-termwise-adjunction-homotopy`,
`lem-weil-pbc-right-adjoint-preserves-kinjective`, and
`lem-sc-bounded-below-injective-resolution`, preserving the remaining approval.

These removals concern this item's proof; no claim is made that other target
branches cease to need these modules. The unit statement and its realized steps
are unchanged.

## Where the brief, the DAG or earlier work was wrong

The old node's Mathlib-search verdict treated identification of the site's derived
adjunction with the generic normalized adjunction as an additional proof obligation.
The current `finiteCoefficientDerivedComparisonAdjunction` definition is explicitly
`(finiteCoefficientComparisonAdjunction T Λ).derivedPlus`. Consequently the existing
normalization lemma applies directly, and the long Hom-localization/resolution-
independence argument need not be reconstructed. Naturality then proves the formula
for every supplied `j`, even without its quasi-isomorphism or injectivity hypotheses;
those hypotheses are used precisely for the two isomorphism assertions.

No statement is disputed or weakened. Edge cases include the zero complex, zero
coefficient ring, and `j` the identity of an injective inverse image: the proof uses
only naturality, localization and the injective comparison and applies uniformly.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
