## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.derivedHomComparison` in
`Sheaf.WeilSheaf.NativeDerivedHomComparison`, keeping its full signature and the
public predicate unchanged. A proved private helper derives all six comparison
clauses from the normalized unit/counit and bijectivity of localization on Hom
into K-injectives. The native proof uses the stated native exactness model,
Mathlib's `CochainComplex.IsKInjective.Qh_map_bijective`, and the existing
`Adjunction.mapDerivedCategoryRightDerivedAdjunction`. Its normalization equations
are `derivedη_fac_app` and `derivedε_fac_app`.

The lift of an invertible arrow is proved invertible by lifting its inverse and
using injectivity twice. The transpose formula follows from the normalized unit
and beta naturality; the resolution equation then follows by right naturality.
Naturality in both variables holds for arbitrary ambient derived arrows.
The existing node's proof and proof_origin now record this shorter argument.

Validation: the complete item compiles through `lcompile.py`; no local Lake or
shared-repository edits were used. The generic helper works without an inhabited
category or nonzero object hypothesis. At identity resolutions the comparison
reduces to the representative transpose; inverse lifts use both K-injective
hypotheses. Zero morphisms and zero objects introduce no extra assumption.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedHomComparison`
(node `lem-sf-native-weil-derived-hom-comparison`).
Added 0 holes and split off 0 statements. No `sorry` remains in the delivered Lean
module. The private theorem `resolutionHomComparison_of_normalizations` is fully
proved. Imported model results keep their existing holes, as intended in stage 3.

## No longer needed

Removed the redundant private import
`Mathlib.Algebra.Homology.DerivedCategory.Basic`; its declarations are supplied by
the retained public imports. Added only the proof import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`.
No public imports were changed. No modules or dependency nodes are withdrawn:
the three existing proof dependencies remain used. The explicit construction of a
new Hom-equivalence family followed by descent through formal localization
inverses is unnecessary because the existing ambient derived adjunction already
provides that family. All required resolution and normalization equations are
proved for that specific adjunction.

## Where the brief, the DAG or earlier work was wrong

The earlier node plan reconstructs an adjunction already supplied by the source
library. The stage-2 review advisory correctly identified the shorter route.
No false statement or interface repair was needed. The unit record has no
realized steps affected by this proof change. Existing declaration docstrings
were preserved. No new nodes, change records, or forced consumer adaptations
were required.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
