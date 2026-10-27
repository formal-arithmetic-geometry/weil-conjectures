## What changed

Replaced the single unfinished proof of `affineSpace_rational_induction` by uniform induction
in the dimension, over every separated finite-type base and every compactification. The step
uses the existing affine-line assertion, explicit coordinate splitting, composition of the
restricted compact-support adjunctions, and ambient tensor/pullback/shift comparisons.
All existing declarations and definitions of the assigned module retain their signatures and
bodies, except for the theorem proof. No adopted source-library module is changed.

Added three modules: `Sheaf.Paper.AffineSpaceRationalGeometry` proves the geometric base and
successor comparisons; `Sheaf.Paper.RationalAffineAdjunctionCalculus` proves open restriction,
composition, and transport of the specified adjunctions;
`Sheaf.Paper.RationalAffineTensorCalculus` records the ambient Tate-power functors and proves
the zero and degree-one comparisons. Its separate preservation/composition theorem remains
unfinished. It concerns ordinary derived inverse image and tensor only, and has no exceptional
inverse image or affine-space induction in its conclusion.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.ProEtale.CondensedRing.affineSpace_rational_induction`
by a real induction from named dependencies. Its proof has no `sorry`.
Added one hole: `AlgebraicGeometry.ProEtale.CondensedRing.rationalAffineTensorCalculus`, node
`lem-sfb-rational-affine-tensor-calculus`. This is a decomposition (one upper hole closed,
one separate lower hole added), not a net hole reduction. No other delivered declaration
contains `sorry`; in particular no definition does.

Proved `rationalAffineZero_isIso`, `rationalAffineSuccIso_over`,
`RationalCompactSupportAdjunction.ofIso`, `rationalOpenCompactSupportAdjunction`,
`rationalCompactSupportAdjunction_comp`, `rationalTatePowerZeroIso`, and
`rationalTatePowerOneIso`. The coordinate isomorphism and all auxiliary functors are actual
constructions. The only use of an arbitrary finite coefficient field in the composition
proof selects a genuine existing field index from its proved `Nonempty` instance; it selects
no mathematical witness from a postponed existence theorem.

## No longer needed

Removed direct proof imports `Sheaf.Paper.UnboundedLocalizingPullback`,
`Sheaf.Paper.CartesianCoefficients`, `Sheaf.Paper.CompactificationCoherenceCocycle`,
`Sheaf.Paper.LocalizingLowerShriekComposition`,
`Mathlib.CategoryTheory.Adjunction.CompositionIso`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` from the assigned module.
The three new helpers provide exactly the interfaces the induction uses. The pullback and
Cartesian results are still mathematical dependencies of the remaining tensor lemma; the
compactification and lower-shriek composition results are used in the proved adjunction helper.
These modules therefore are not proposed for withdrawal.

The proof no longer needs the general exceptional-adjoint existence theorem
`sk-prop-sf-existence`: it constructs every required adjunction from the open and affine-line
adjunctions and composes them. Removed that obsolete entry from `tool_uses`. Its occurrence
in the unchanged mathematical statement and its existing public imports are retained.
No module is withdrawn; no adopted source declaration is removed. The unit route through
the affine-line theorem and induction is preserved. No other node is proposed for pruning.

## Where the brief, the DAG or earlier work was wrong

The induction argument is mathematically consistent, but its steps labelled elementary hide
substantial sectionwise/internal tensor transport and local constructibility work. The new
ambient tensor lemma isolates those statements rather than claiming their proof follows from
adjoint uniqueness. The supplied affine-line assertion records the localizing adjunction but
not preservation of bounded constructibility, so its restriction alone does not prove the
second conclusion in higher dimension. The separate tensor-preservation argument is needed.

The source file currently exists despite an older quarantine/rework row. Its existing
signatures and definitions were preserved; neither its archive nor any Lean path is deleted.

## New nodes

`lem-sfb-rational-affine-geometry` records the proved coordinate splitting and zero-dimensional
projection, using the existing affine-space reindex and sum APIs.

`lem-sfb-rational-affine-adjunction-calculus` records the proved restricted open adjunction and
composition calculation, including the precise ambient comparison isomorphisms.

`lem-sfb-rational-affine-tensor-calculus` records the independent ambient positive Tate-power
preservation and composition assertions, their complete proof in words, and the proved
zero/degree-one comparisons. Its statement applies to arbitrary composable morphisms over k
and contains no affine-space exceptional-adjoint assertion. The original node's proof route
now lists these three separate calculations and the existing affine-line result.

No existing definition or statement changed, so no change record is required.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
