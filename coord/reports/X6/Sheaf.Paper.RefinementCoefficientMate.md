## What changed

Replaced the sole `sorry` in `lean/Sheaf/Paper/RefinementCoefficientMate.lean`.
The coefficient conjunct applies
`AlgebraicGeometry.Etale.properOpenComparison_coefficient_refinement` verbatim.
For the site conjunct, expand `ProEtale.properOpenProEtaleIsoPlus` and cancel the
initial open-site comparison with its inverse using `Iso.hom_inv_id_app_assoc`.
The remaining factors are precisely the asserted right side. Removed 18 unused
proof-only imports from the current source. No declaration, statement, definition,
public import or visibility changed. Updated the item's
DAG proof, proof dependencies and proof origin to record this shorter argument.

The existing `lem-weil-pbc-proper-open-comparison-proetale` is used as a generic
tool: its explicitly defined transport is the very pro-etale arrow appearing in
the assigned statement. Its module was already publicly imported. This preserves
the unit's coefficient-compatibility route and changes no unit statement or step.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.refinementCoefficientMate`
(node `lem-sp-refinement-coefficient-mate`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered Lean module. The coefficient-refinement
premise remains an existing named theorem with `sorry` in its own module; this
delivery does not claim that premise or the transitive dependencies are proved.
The site equality uses a definition and ordinary isomorphism cancellation.

Validation: the complete module compiled through `lcompile.py`. Both conjuncts
retain all original hypotheses, including the separate bound for scalar extension;
no flatness or cartesian hypothesis is introduced. The final cleaned proof is
checked again by the delivery dry run and its declaration/axiom probe.

## No longer needed

Both original public imports are retained because the statement uses their named
maps. Removed the following 18 proof-only imports present in the current source;
the completed proof compiles without them:

- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ClopenSectionComponent`
- `Sheaf.AlgebraicGeometry.ClopenSectionDirectImage`
- `Sheaf.AlgebraicGeometry.DerivedOpenRestriction`
- `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.ProperOpenComparison`
- `Sheaf.AlgebraicGeometry.ProperOpenSection`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

No module is claimed to leave the targets' actual import closure.
The following original proof dependencies are unnecessary as direct premises of
this item, because the coefficient normalizations are already those of the cited
coefficient theorem and the site arrow is already defined by explicit transport.
Their underlying modules may remain transitively required by the two imports:

- `lem-weil-pbc-extension-by-zero-adjunction`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-proper-open-section`
- `lem-weil-pbc-proper-open-p-proper`
- `lem-weil-pbc-extension-by-zero-exact`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-exact-functor-bounded-below`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-etale-sheaf-clopen-product`
- `lem-sp-clopen-section-component`
- `lem-weil-pbc-localization-universal-property`
- `lem-weil-pbc-comparison-pullback`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-cbc-extension-zero-base-change`
- `lem-sf-open-tensor-normalization`
- `lem-weil-pbc-derived-open-restriction`
- `def-kun-unbounded-exchange`
- `lem-weil-pbc-comparison-direct-image-canonical-mate`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-clopen-section-direct-image`
- `def-weil-pbc-composite-adjunction`
- `def-weil-pbc-adjunction-mate`
- `def-weil-pbc-proper-open-comparison`
- `prop-exc-open-adjoint`

Removed their obsolete top-level `tool_uses` entries, preserving the order of the
remaining entry. No DAG node is deleted. No new module or node is added.

## Where the brief, the DAG or earlier work was wrong

The original DAG's eleven-step calculation is longer than needed for the recorded
Lean statement. The statement already uses the exact coefficient-refinement maps
and the pro-etale comparison defined as the four-factor transport, so the site
square follows by cancellation. This is a shorter proof of the unchanged assigned
Lean statement; no assertion is made here about independently reconstructing a
pro-etale theta by other constituents. The existing stage-2 normalization and
statement review remain the basis for that mathematical identification.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
