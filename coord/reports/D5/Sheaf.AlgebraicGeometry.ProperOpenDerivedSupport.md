## What changed

Proved `AlgebraicGeometry.Scheme.isIso_proper_open_derived_support` in
`lean/Sheaf/AlgebraicGeometry/ProperOpenDerivedSupport.lean`, with its original signature,
universes, coefficient category and actual adjunction counit unchanged. No other Lean module
is changed. All original public imports are retained.

Change record: `coord/changes/D5-proper-open-derived-support-proof-context.md`
documents the scoped proof commands and the unchanged interfaces of all 195 consumers.

The proof uses the existing proper/open sheaf comparison after factoring j₁ through the
pullback of j₂. It computes bounded-below direct images on open-extended injectives, proves
open extension preserves countable products using the fixed-scalar open-closed sequence,
and applies the recorded Postnikov convergence theorem. Fully faithful open extension has
image closed under the resulting homotopy-limit cones; this proves invertibility of the
specified counit without choosing a new counit or asserting canonical uniqueness of third
arrows of triangles. The generic glue is proved in private helpers in the same module.

The local instances fix sheafification, locally bijective equivalences and the ordinary
standard localization to the existing coefficient universes. Integral-coefficient instances
with unconstrained max-universe parameters are disabled in this proof scope. No new global
instance, definition data, axiom or statement is exported.

Updated `lem-sp-proper-open-derived-support`'s proof, proof dependencies and origin to match
this argument. The unit's statement and realized proof steps remain unchanged.

Validation: the full item compiled without errors or warnings through lcompile.py; final
delivery preflight is recorded by deliver3.py.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.isIso_proper_open_derived_support`
(blueprint: `lem-sp-proper-open-derived-support`).

No `sorry` remains in the item, and the delivery adds zero holes and zero split statements.
This is a proof from existing named declarations: their existing postponed proofs remain
separate items. All private helper theorems and definitions in this packet are complete.

## No longer needed

Removed direct imports (some remain available transitively or are used by reused lemmas):

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Sheaf.Algebra.Homology.KInjectiveProducts`
- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`
- `Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageFormula`
- `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero`
- `Sheaf.CategoryTheory.SiteTruncationDerivedLimit`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.RingTheory.WContractibleClosedLocalization`
- `WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`

The item's proof no longer directly needs these old planned dependencies:

- `lem-exc-closed-inverse-image-formula`
- `lem-weil-pbc-affine-closed-site-functor-properties`
- `def-weil-proper-morphism`
- `lem-weil-pbc-proper-base-change`
- `lem-pc-quasi-compact-base-change`
- `lem-weil-pbc-wcontractible-closed-localization`
- `lem-weil-pbc-ind-etale-stability`
- `def-weil-pbc-proetale-covering`
- `lem-weil-pbc-proetale-shriek-specialization-zero`
- `lem-weil-pbc-closed-immersion-base-change`
- `def-weil-closed-immersion`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-weil-proetale-countable-products-exact`
- `lem-weil-pbc-proetale-affine-wcontractible-covering-family`
- `lem-kun-site-truncation-derived-limit`

The sheaf comparison packages the original boundary-specialization work; the stronger
proved exact-products theorem replaces the separate countable-products statement; the
recorded Postnikov convergence theorem replaces the general site-truncation criterion and
its explicit weakly contractible-cover hypothesis. Derived products use the existing
sorry-free TowerLimit implementation rather than the two holed product helper modules.
The ringed open-closed statement is replaced here by the existing fixed-scalar sequence.
The final support argument uses full faithfulness and homotopy limits, so needs no second
closed-localization argument. This is pruning of this item's direct obligations, not a claim
that these modules leave the entire targets' import closure.

Obsolete existing tool-use approvals were removed precisely when their nodes ceased to be
proof dependencies, preserving the order of the retained approvals.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was weakened or disputed. The original ten-step docstring records
the longer plan; the updated DAG records the actual shorter Lean argument. No elementary
identification of the actual counit with an independently selected map is assumed: essential
image criteria for the specified fully faithful adjunction give its invertibility.

The interrupted sandbox contained a complete proposed argument but invalid `private section`
syntax, prematurely closed namespace scope, ambiguous integral-coefficient universe
inference, and two mapping-cocone naturality/triangle identities still requiring proofs.
These are repaired. The resumed dry run found no completed earlier delivery and
requested the scoped-command change record supplied in this packet.

Requests for the independent reader's tool-use review: `det-pe-products-exact` and
`det-pe-left-complete-iso` are the general pro-etale products/convergence results; their
statements apply to the actual module sheaves and strict lower-truncation complex here.
`lem-sf-proetale-open-closed-sequence` is the generic fixed-scalar localization sequence.
`lem-pc-homotopy-limit-map` is generic triangulated-category glue. None asserts the present
proper/open support conclusion, and no import cycle is introduced. The existing
`lem-exc-proetale-proper-open-sheaf-comparison` belongs to this item's own unit.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
