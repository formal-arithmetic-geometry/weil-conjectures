## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.properIntegralRationalScalarComparison_isIso`
without changing any existing public signature. The proof factors the
coefficient inclusion through F, applies the localized direct-image comparison to the
bounded-below input, and uses the source library's proved finite-subfield push comparison.
Private helpers lift the restriction-square composition identity to derived categories,
paste its mates, and identify the resulting arrow with the specified counit transpose.
The existing unit route and proper closed-complement coefficient calculation are retained.

To avoid repeated unfolding of the concrete derived-adjunction expression, the comparison
body now uses the existing `derivedPushHom` component. Its coefficient map and flatness
proof are the same as those of `integralRationalScalarPullIso`. The private proved
`push_counit_formula` identifies this restriction-square mate with exactly the previous
geometric counit transpose. All other public definition bodies remain verbatim.
The change record is `coord/changes/proper-integral-rational-comparison-mate.md`.
The consumer check found no current downstream Lean modules; DAG parents are retained.
The definition change reopens target-definition review under the stage-3 rule.

The current unit record realizes its statement and both proof steps through
`prop-compactification-coherence-detailed`; this delivery changes none of them.

The module disables only the `privateModule` linter: this file explicitly exports five
declarations, and that redundant check otherwise enumerates its large private environment.
All other linters and kernel checks remain enabled.

All existing public imports are retained. The proof adds private imports of
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`,
`WeilConjectures.CategoryTheory.DerivedExactCompositionComparison`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.

## Proved and sorry left

Closed the sole hole in
`AlgebraicGeometry.ProEtale.CondensedRing.properIntegralRationalScalarComparison_isIso`.
Item holes: 1 before, 0 after. Holes added: 0. No split-off statements.

Validation: the complete proof with the delivery axiom probe compiled in 39.9 seconds
through `lcompile.py`, reporting no unexpected axioms. The diagnostic's only warning
concerned the appended probe's own long line. All five public declaration signatures
and all public imports are verbatim preserved. The consumer search reports zero
downstream Lean modules. Five earlier delivery attempts exceeded the compile limit
and pushed nothing. The final version keeps the structural instance cache, narrows an
associativity simplification to the relevant hypothesis and goal, and checks declarations
sequentially. Disabling the optional backward-unification attributes also compiled
the complete proof in 43.8 seconds with ordinary unification. No kernel check or axiom check is disabled. No new node or public lemma
is added. Delivery preflight and independent review remain pending.

## No longer needed

Removed these private proof imports:

- `Sheaf.Paper.SectionDerivedPushpullNormalization`.
- `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates`.
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`.
- `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`.
- `Sheaf.CategoryTheory.PastedMatesCounitNormalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.AlgebraicGeometry.ProperBasic`.

This proof does not use the planned nodes
`lem-pd-section-derived-pushpull-normalization`,
`lem-sfb-internal-section-scalar-adjunction`,
`lem-sfb-local-field-integral-basis`,
`lem-sfb-derived-finite-free-scalar-coordinates`,
`lem-sfb-topos-finite-free-counit-comparison`, or
`lem-sfb-topos-scalar-mate-transitivity`.
The finite-extension source comparison replaces the finite-coordinate argument;
the remaining composition and counit identities follow directly from generic
localization and mate calculus. The proof also does not directly need
`lem-sfb-finite-free-scalar-coordinates`,
`lem-sfb-pasted-mates-counit-normalization`,
`lem-weil-pbc-ring-sheaf-change-adjunction`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, or `pqf-lem-proper-basic`.
Properness supplies quasi-compactness and quasi-separatedness through the existing
Mathlib instances. Obsolete corresponding tool-use entries are removed from the node.

`lem-sfb-kflat-scalar-comparison-normalization` and
`lem-sfb-internal-module-operations-transport` remain statement dependencies and
public imports of the unchanged interface. No globally unreachable module is
claimed: some removed imports can still occur transitively in preserved dependencies.
No source-library declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned section-module/finite-coordinate proof is unnecessary for this item:
`isIso_derivedPushHom_padicSubfieldRingObjMap` already proves the exact finite-field
comparison on every unbounded input and every scheme morphism. The node's proof
and proof dependencies are updated to the actual internal-module argument.
The public theorem and its hypotheses are unchanged. The cross-unit uses are the
already proved finite-subfield coefficient tool and generic derived-composition and
Mathlib localization/mate tools; they do not replace a geometric unit step.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
