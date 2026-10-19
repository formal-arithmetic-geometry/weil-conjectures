## What changed

Proved `ellAdic_proper_lowerTail_bound` without changing its statement. Its proof uses
cohomology of the localizing hull, a uniform upper-amplitude argument, and the actual
Postnikov derived-limit triangle. The Postnikov upper-amplitude proof allows one extra
degree, which is harmless for the item's existential natural bound. The retained
Postnikov reconstruction, ind coproduct closure, locally-free constant-model comparison,
and upper-amplitude arguments are proved. The item docstring now describes this actual
argument and its extra degree.

Continued both earlier split obligations: proved weak Serre closure for every continuous
finite normed coefficient field, including transport from arbitrary finite extensions to
canonical subfields. Proved the proper heart bound for those fields and for PadicAlgCl.
Also proved extension of any constructible-heart proper bound to ambient ind objects by
bounded-below filtered continuity. Restriction of scalars transports finite presentations,
ambient ind objects, kernels, cokernels, extensions, derived direct images and homology.

Completed both integral obligations as well. The integral heart bound uses the bounded-above
clause of `integralProperDirectSums`, an actual comparison of integral coefficient models,
and explicit transport from any embedded finite extension to its canonical image field.
Integral weak Serre closure uses degree-zero and degree-one Ext/Hom continuity, finite
presentation, finality of finite-stage presentations, and the generic finite-stage
kernel/cokernel and extension constructions. No uniform Ext bound is needed.
No existing public signature or definition changed.

## Proved and sorry left

The item originally contains one hole, closed here:
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_proper_lowerTail_bound`.

Also proved every formerly split obligation:

- `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_finite_indConstructible_weakSerre`;
- `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_proper_heart_upper_bound`;
- `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_integral_indConstructible_weakSerre`;
- `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_integral_constructible_heart_upper_bound`.

The other new modules prove `ellAdic_proper_pushforward_isLE_of_isLE`,
`ellAdic_indConstructible_heart_closure`,
`DerivedCategory.lowerTruncation_isDerivedLimitTriangle`,
`CategoryTheory.ObjectProperty.ind_isClosedUnderCoproducts`, and
`constructible_eq_constantModels_of_lfp_locally_free`.

Original holes closed: 1 of 1. Holes added: 0. Sorries left in all ten delivered Lean
modules: 0. No statement is split off with a hole, and no definition contains sorry.
Existing stated dependencies may still have their own sorries, as permitted by stage 3.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound`
- `Sheaf.Paper.AmbientIndDerivedSums`
- `Sheaf.Paper.AmbientIndDerivedTriangulated`
- `Sheaf.Paper.IntegralConstructibleCompactness`
- `Sheaf.Paper.IntegralProperDirectSums`
- `Sheaf.Paper.ProperHeartBound`
- `Sheaf.Paper.ProperIndConstructibleUnbounded`

The direct arbitrary-complex route through `det-proper-unbounded-window-arbitrary` and
`det-prop-int-compactness-direct-sums` is replaced by the proved Postnikov argument in the
item and upper-amplitude module. The generic `lem-sfb-left-complete-heart-upper-bound`,
`det-ambient-ind-derived-sums`, `det-ambient-ind-derived-triangulated`, and the direct
finite-type fibre-bound import are not used by that proof. The heart-bound proof still uses
`sk-lem-proper-heart-bound` for the rational branches; the proved integral bound
uses `det-prop-int-compactness-direct-sums`. These latter dependencies are therefore
not claimed globally pruned. No blueprint unit statement or realized proof step is bypassed.
The integral weak Serre proof also avoids `det-prop-int-compactness-compact` and its
`Sheaf.Paper.IntegralConstructibleCompactness` API: degree-zero and degree-one continuity
suffice, and work over the stated arbitrary base field.
No whole module is claimed removed from the global Challenge import closure; the lists
above are removals from this proof route. Exploratory scratch modules are outside the
delivery's lean tree and are not delivered.

## Where the brief, the DAG or earlier work was wrong

Source constructibility means local finite presentation on strata. Several Paper APIs use
finite constant scalar models instead. The rational branches now prove the required
comparison using finite local freeness; no such comparison is silently assumed. The
coefficient certificate permits arbitrary normed finite extensions, whereas the Paper
interfaces use canonical finite subfields. The delivery constructs actual continuous
coefficient isomorphisms and transports the module categories and derived direct images.

The integral compactness API requires a uniform Ext bound. The available
`integralConstructibleExt` bound assumes a finite base field, while this item allows an
arbitrary field of positive prime characteristic. It cannot supply that input here.
The proved integral weak-Serre argument instead uses only Ext/Hom continuity, for which the
existing `integralExtHomContinuous` has the correct general-base-field hypotheses.

## New nodes

`new-lem-sfb-adic-proper-upper-amplitude` records the proved passage from a heart bound
to the upper bound on arbitrary ind-cohomological complexes, using lower truncations.

`new-lem-sfb-exact-products-postnikov-limit` records the proved canonical Postnikov Roos
triangle with the actual truncation projections under exact countable products.

`new-lem-sfb-adic-proper-heart-upper-bound` records the proved coefficient case split,
continuous coefficient transport, algebraic-closure bound and integral filtered extension.

`new-lem-sfb-adic-ind-heart-closure` records the proved closure and localizing-hull argument.

`new-lem-sfb-adic-ind-heart-weak-serre` records the proved continuous-field argument and
its assembly with the separate integral assertion.

`new-lem-sfb-lfp-free-constant-comparison` records the proved equality of constructibility
predicates under the stated local finite freeness hypothesis.

`new-lem-sfb-ind-coproduct-closure` records the proved finite-partial-coproduct filtered
presentation for ambient ind objects, including the empty coproduct.

`new-lem-sfb-integral-ind-heart-weak-serre` records the proved integral closure argument:
finite scalar comparison, essential smallness, finite presentation from Hom continuity,
canonical presentation, and kernel/cokernel and extension assembly from finite stages.
It imposes no finite base-field or completeness hypothesis on ind objects.

`new-lem-sfb-integral-constructible-heart-bound` records the proved proper bound for
constructible integral heart objects, extracted from the existing integral proper theorem
and transported by explicit continuous coefficient isomorphisms.
The resumed compile exposed expensive elaboration in the integral coefficient comparison.
Removed a redundant refinement and used declaration-local backward elaboration settings
to keep the existing definitions behind their APIs; no definition or signature changed.

The resumed delivery records the successful LeanSearch queries already present in the sandbox
search log and gives the Postnikov node an exact local Stacks source and lemma labels.
There are no definition/signature repairs or forced adaptations, so no change record is needed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
