## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.exists_brownExceptionalAdjoints` in `Sheaf.Paper.BrownExceptionalAdjoint`. The proof constructs the restricted lower-shriek functors, applies the locally-small Brown representability theorem, obtains exact right adjoints and proves their uniqueness, then lifts the compactification cocycle through the full-subcategory inclusion and transfers it to the right adjoints with the private `coherentRightAdjoints` lemma. Change record `coord/changes/brown-exceptional-refinement-map.md` records that the refinement-map definition now delegates to the existing canonical `compactificationRefinementComponent`; this removes a costly duplicate dependent expression while preserving its public type and meaning. The coherence-cocycle import is public for that definition dependency.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.ProEtale.CondensedRing.exists_brownExceptionalAdjoints` (node `det-sf-existence-brown`). Added 0 holes; split off 0 holes. No sorry remains in the item module.

## No longer needed

The proof does not use the direct imports `Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint`, `Mathlib.CategoryTheory.Yoneda`, `Sheaf.Compactification.BoundaryRefinement`, or `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`; they remain removed from the proof-only import list. No proof dependency node is bypassed: Brown uses the existing locally-small specialization, and compactification comparisons use the existing coherence-cocycle and identity declarations.

## Where the brief, the DAG or earlier work was wrong

The generic Brown criterion has a larger coproduct universe than the theorem's local-small hypothesis; `brownHomRepresentabilityLocallySmall` is the required universe-transfer result. The earlier explicit refinement-map body was definitionally awkward despite being mathematically the same canonical component, so the definition repair records the canonical delegation.

## New nodes

None.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
