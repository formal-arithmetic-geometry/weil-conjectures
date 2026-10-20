## What changed

Proved `AlgebraicGeometry.Etale.geometricPoint_derivedSections_adjunction`, including both
its specified unbounded counit equation and its degree-zero inverse-germ normalization.
Private helpers perform adjunction transport, the sheafification calculation of the germ,
and compatibility of exact-right derived composition with single-complex augmentations.
The unit's geometric-point and pullback-of-constants route is retained.

Added private proof imports of `CompConjugate`, `RightDerivedSingleZeroUnit`,
`DerivedExactCompositionComparison`, and the source `Sites.Point.ConstantSheaf` module.
Updated the existing node's proof, proof dependencies and proof origin to match Lean.

Constructed `geometricPointSectionsConstantAdjunction` and
`geometricPointSectionsImageAdjunction` directly with the exact-left/right-derived API.
The proved private `canonicalDerivedAdjunction_eq` identifies this construction with
the old transported left-derived adjunction by equality of units. This prevents
expensive concrete expansion of the flat-resolution construction. All public signatures
stay unchanged. Change records:
`coord/changes/geometricPointSectionsConstantAdjunction.md` and
`coord/changes/geometricPointSectionsImageAdjunction.md`.
`tools/downstream.py --uses` finds only this item as a direct user of either definition;
all thirteen transitive importers retain their interfaces and need no forced adaptation.

Validation: the complete module compiled cleanly through `lcompile.py` in 27.0 seconds
before documentation cleanup. The delivery dry run additionally checks the final packet.
The first dry-run compile timed out under its probe. The two H⁰ comparison bodies
were then factored through generic definitions with the same formulas, preserving
definitional equality and reducing repeated checking at concrete sheaf categories.
Additional records: `coord/changes/geometricPointSectionsImageH0Iso.md` and
`coord/changes/geometricPointSectionsGlobalH0Iso.md`. The two generic construction
helpers are attached to the existing node and introduce no proof obligations.
The private `comparison_zero_factored` reuses the proved augmentation calculation
with those factored comparisons, avoiding concrete unfolding in the main proof.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.geometricPoint_derivedSections_adjunction`
(node `lem-kun-geometric-point-derived-sections-adjunction`). Both conjuncts are proved.
There are zero `sorry` occurrences left in the item, zero holes added elsewhere, and no
split-off statements. Every new private helper is proved. Imported declarations remain
their original library statements; their proofs were not changed in this packet.

## No longer needed

Removed these redundant direct proof imports:

- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Mathlib.CategoryTheory.Abelian.RightDerived`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Mathlib.CategoryTheory.Adjunction.Unique`
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Removed direct proof dependencies
`prop-weil-pbc-kinjective-resolutions-exist`,
`lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`, and
`lem-weil-pbc-bounded-below-injectives-kinjective`.
No resolution is selected in this proof: the existing derived-conjugation and single-unit
APIs perform the needed normalized computations. The corresponding K-injective-existence
top-level `tool_uses` approval is removed. These general results can still occur inside
imported APIs; this packet does not claim they are globally unnecessary.
The termwise-adjunction and K-injective-preservation dependencies remain because the
source derived-conjugation theorem uses them. The other removed imports provide
infrastructure already exported by retained statement imports or the new proof APIs.
No module is withdrawn; no claim of additional globally pruned modules is made.

## Where the brief, the DAG or earlier work was wrong

The original resolution-level plan is valid but longer than necessary given the proved
source APIs. The proof reuses those APIs and proves the remaining normalization glue.
No mathematical statement was weakened or disputed. The two adjunction implementation
changes preserve the normalized structures by the explicit equality proof.
The standalone exact-composition comparison is now exported by
`WeilConjectures.CategoryTheory.DerivedExactCompositionComparison`; its current theorem
name is `rightDerivedFunctorCompMapDerivedCategoryIso_eq_viaRightDerived`.

Dispatcher metadata observation: the original session record had start
`1792446789.206728`; after the provider-error resumptions the sandbox record has
start `1792499362.839907`. I did not edit either budget record and have continued
against the original session's safety deadline. No wait or unchanged retry was used
to pass a split-off gate; there are no split-off holes.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
