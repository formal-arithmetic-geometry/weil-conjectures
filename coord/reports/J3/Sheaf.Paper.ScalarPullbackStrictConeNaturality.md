## What changed

Replaced the single `scalarPullbackStrictConeNaturality` hole by an assembly of
strictly smaller construction and coherence lemmas. The written proof builds
the tensor/Roos comparison from `scalarRoosMap`, proves its invertibility on
both mapping-cocone coordinates, and proves its uniqueness. It descends the
resulting strict cone map using fully faithful precomposition with the good
complex localization, proves the exact published descent equation, and obtains
uniqueness by cancellation. These three uniqueness arguments prove the
subsingleton assertion for the bundled data. The cone argument is proved
first for arbitrary additive functors and tower functors. Matching functor
parentheses and using explicit associators in descent keeps the implementation
within the file time limit, with transparency checking enabled. A typed
private counit transformation and its application lemma keep the concrete
cochain model from being unfolded repeatedly in the descent construction;
the focused optimized descent compile passed in 38 seconds.

`FiniteFreeScalarCochainProperties` reuses the library's finite-free exactness
and product argument, the independent-universe K-flat change-of-rings theorem,
and the universal left-derived-functor criterion. It proves product preservation,
preservation of good complexes, and invertibility of the scalar counit on all
complexes, including the possibly non-K-flat pullback Roos complex.

Moved the original thirteen auxiliary definitions verbatim to
`ScalarPullbackStrictConeData` and publicly re-exported them from the original
module. This permits independent split modules without a circular import.
A byte-for-byte comparison of the entire thirteen-definition block with the
original succeeds. Original public names, signatures, definition bodies, fields
and mathematical statements are unchanged. The existing generator definition node now points to
its new physical module. The original five public imports remain available
through the re-export. No source-library declaration is changed.

Validation: all six packet modules compile with `lcompile.py`. The final clean
check accepted `ScalarPullbackUniqueDerivedDescent`, the item, and the unchanged
direct consumers `ExplicitScalarConeWordCoordinates` (M8) and
`IsomorphismScalarAugmentationCone` (R6), with the 60-second gate in force.
The other four supporting modules passed the earlier full packet compile.
No forced adaptation is needed. Both temporary consumer copies were verified
unchanged against current source and removed before delivery. No profiling
options remain.

## Proved and sorry left

Original holes: one. Closed in the item:
`WeilConjectures.scalarPullbackStrictConeNaturality`. This is a decomposition,
not a sorry-free proof of the full mathematical result: two strictly smaller
holes are added. Within this packet, holes closed minus holes added is -1;
two packet holes remain. The delivery ledger determines the full target-closure count.

The new finite-free scalar cochain property is proved without a local `sorry`.
The cone construction and two-coordinate uniqueness are proved private helpers
in the item. Derived descent and its uniqueness are proved in the separate
`ScalarPullbackUniqueDerivedDescent` module; that separation adds no hole.
No `sorry` remains in the item or in a definition.

Every remaining hole introduced by this packet:

- `WeilConjectures.scalarPullbackStrictTower_existsUnique`, node
  `lem-sf-scalar-pullback-strict-tower-construction`, in
  `Sheaf.Paper.ScalarPullbackStrictTowerConstruction`. This is only the
  balanced strict tower map, with no cone or derived descent assertion.
- `WeilConjectures.scalarPullbackStrictCoherence`, node
  `lem-sf-scalar-pullback-strict-coherence`, in
  `Sheaf.Paper.ScalarPullbackStrictCoherence`. This is only the ordinary
  association and identity calculation on supplied data, with no existence
  or uniqueness assertion for the data or derived maps.

Both statements have complete proofs in words and their source in their
own docstrings and DAG nodes. Edge cases checked: identity coefficients,
identity scheme morphism, zero complexes, empty schemes, first positive
quotient exponent, unbounded complexes, and ramified coefficient inclusions.
No claim that a ramified finite quotient inclusion is flat is used.

## No longer needed

Removed the following original direct proof imports from the item:
`Sheaf.CategoryTheory.StrictRoosModel`,
`Sheaf.CategoryTheory.StrictRoosHomotopyFunctor`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and
`Mathlib.CategoryTheory.Localization.Predicate`. The localization argument
in `ScalarPullbackUniqueDerivedDescent` reuses the proved helper from
`FiniteFreeCompletedScalarComparison` instead of reproving fully faithful
precomposition here.

The explicit homotopy/resolution descent steps are unnecessary here: the
already-proved good-complex localization and canonical comparisons give
unique descent directly. Thus the main node no longer directly needs
`lem-pc-kflat-resolution`, `lem-pur-kflat-change-of-rings`,
`lem-pur-strict-roos-homotopy-functor`,
`lem-weil-pbc-exact-functor-derived-factorization`, or
`lem-weil-pbc-site-derived-tensor-descent`. The independent-universe
K-flat change-of-rings lemma is used in the new finite-free lemma instead.
These modules remain wherever other declarations use them; no module is
withdrawn and no whole-target-closure pruning is claimed.

The other old direct proof dependencies are retained transitively through the
new definition/property/construction lemmas: `def-pur-integral-derived-operations`,
`def-pur-sheaf-tensor-product`, `def-weil-abstract-derived-category`,
`def-weil-integral-scalar-extension`, `def-weil-proetale-inverse-image`,
`def-weil-strict-roos-model`, and
`lem-weil-finite-free-completed-scalar-comparison`. Their absence from the
main node's direct list is a dependency relocation, not a claim of pruning.
The proved descent module now carries the direct uses of
`lem-pur-integral-operations-well-defined`, `lem-pur-derived-change-of-rings`,
and `lem-weil-pbc-localization-universal-property`; these are also retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement correction was needed. The existing
argument is realized with the library's more recent normalized scalar-cochain
model and good-complex localization APIs. Those APIs avoid repeating the
homotopy-level construction from the old prose plan. The unit route and the
original theorem statement are preserved. The definition move only enables
imports of strictly smaller subproblems.

## New nodes

`def-sf-scalar-pullback-strict-cone-data` gives definition ownership to the
twelve existing auxiliaries not already owned by
`def-pod-scalar-pullback-generator`; all thirteen definitions move verbatim.

`lem-sf-finite-free-scalar-cochain-properties` is the proved finite-free
unbounded scalar property. It uses the generic finite-free quotient Roos
module only as a proved tool for exactness/products, not its ramification or
cofinal-completion construction.

`lem-sf-scalar-pullback-strict-tower-construction` records Steps 1–3 of the
original argument as one genuine strict tower construction obligation.

`lem-sf-scalar-pullback-strict-coherence` records the original Step 10:
ordinary tensor association and both-coordinate composition/unit equations.

`lem-sf-scalar-pullback-unique-derived-descent` is the proved localization
step with the exact canonical counit equation. It is in a separate module after
removing the costly implicit functor-association conversions; the complete
combined file checked in 63 seconds, so separation respects the unchanged
60-second limit. This node introduces no `sorry`.

Change record: `coord/changes/J3-scalar-pullback-strict-cone-factorization.md`.
All new nodes inherit the original chapter, unit and nearest blueprint ancestor.
Blueprint-wide searches for scalar pullback, strict cone and scalar coherence
found no exact existing blueprint statement. The finite-free search found
broader coefficient lemmas, which do not assert these three particular
cochain-functor properties together. Mathlib searches are recorded from the
actual launcher search log. No separate second reader was started, as required
by this dispatcher brief.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
