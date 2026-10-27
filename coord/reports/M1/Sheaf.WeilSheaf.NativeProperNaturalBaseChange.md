## What changed

Replaced the sole hole in `Sheaf.WeilSheaf.NativeProperNaturalBaseChange` by a complete
assembly proof with the original signature. The proof constructs the canonical ambient mate,
forgets its Frobenius structure, transfers boundedness and constructible cohomology through
the exact homology comparison, conjugates the geometric component by the specified comparison
isomorphisms, reflects invertibility, and obtains a natural isomorphism by whiskering and
`asIso`.

Added `Sheaf.WeilSheaf.GeometricProperBaseChange`, with the actual geometric pullback square
and derived mate, and `Sheaf.WeilSheaf.NativeBaseChangeForgetComparison`, with the actual
native mate and canonical pullback/direct-image forgetting comparisons. Every data definition
is explicitly constructed from existing operations and adjunctions. The geometric support
module imports `WeilSheaf.Category` directly and does not need `WeilSheaf.LowerShriek`.
The source library already
provides the derived adjunction and coherent native pullback composition isomorphisms.

The remaining eight-step argument is decomposed into two statements: equality of the forgotten
mate on arbitrary commutative squares (no properness or constructibility), and invertibility of
the geometric mate on bounded constructible adic inputs (no Weil structure). Their docstrings
and new nodes give the full argument and preserve the original affine-chart/rational-PBC route.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.nativeWeil_proper_natural_baseChange` (1 of 1).
Added two named holes:

- `AlgebraicGeometry.NativeBaseChange.forget_mate`
  (`lem-sf-native-base-change-forget-comparison`).
- `AlgebraicGeometry.NativeBaseChange.geometric_proper_baseChange_isIso`
  (`lem-sf-geometric-native-proper-base-change`).

This is a decomposition, not a sorry-free proof of the mathematical theorem: 1 upper hole
closed, 2 lower holes added, 0 holes left in the assigned module, 2 holes in the delivery.
All intervening definitions and the final combination have complete Lean bodies.

Validation: `lcompile.py --all` compiled all three delivery modules in import order with
exit code 0 and no warnings. The statement parser confirms that all three node attachments
match their Lean declarations and that the original theorem signature is unchanged.
All original public imports are preserved; all Lean lines fit the 100-character limit.
The delivery tool records its independent compile and preflight results.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.Paper.NativeAdicEncodingCore`
- `WeilConjectures.SixFunctors.ProEtale.Adic.Constructible`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison`
- `Sheaf.CategoryTheory.DerivedCategory.RightDerivedFromAdaptedComplexes`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero`
- `Sheaf.Paper.NativeModuleConstructibilityComparison`
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`
- `Sheaf.Paper.FiniteSpanModuleDerivedComparison`
- `Sheaf.Paper.ProperBaseChangeRational`
- `Sheaf.Paper.SheafSliceDerivedComparison`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`

Their mathematical content, where needed, remains in the two split statements' proof plans;
this delivery claims no global module withdrawal. Some imports remain transitively available
through the native framework. The parent now cites the two split nodes, the native framework,
the mate definition, native exactness, and fixed-pair conservative forgetting. The following
old direct parent proof dependencies are no longer direct dependencies (they are recorded
below the appropriate split node instead):

- `lem-sf-native-adic-encoding-ordinary-operations`
- `lem-pur-ringed-site-grothendieck-abelian`
- `lem-weil-pbc-ringed-topoi-module-adjunction`
- `lem-sf-fixed-pair-adjunction-lift`
- `lem-sfb-grothendieck-k-injective`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-pc-derived-adjoint-functors`
- `lem-kun-derived-adjoint-square-comparison`
- `lem-sf-right-derived-from-adapted-complexes`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-sf-ringed-restriction-exchange-open-descent`
- `def-weil-proper-morphism`
- `def-weil-finite-type-morphism`
- `lem-weil-pbc-proper-base-change`
- `lem-sc-separated-over-affine-scheme-separated`
- `lem-sfb-finite-type-composition-base-change`
- `lem-pod-separated-finite-type-base-change`
- `lem-sf-native-adic-constructible-pullback`
- `lem-weil-pbc-qcqs-over-affine`
- `lem-sf-native-adic-qcqs-stratification`
- `lem-sf-weil-verdier-module-constructibility-comparison`
- `det-def-sfb-constructible-local-model`
- `lem-sf-finite-span-module-derived-comparison`
- `det-thm-sfb-proper-base-change-rational`
- `lem-sbc-ringed-topos-sheaf-slice-derived-comparison`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`

The parent's obsolete `tool_uses` entries were removed along with their direct dependency
edges; the retained fixed-pair comparison remains directly used. No source declaration,
public import, target statement, unit step, or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG's lengthy derivation of the native
adjunction and Frobenius-compatible pullback composition is already implemented in the
adopted source library (`RightDerivedFunctor.Adjunction`, `UpperStarComp`, `UpperStarId`,
and `UpperStarLowerStarAdjunction`). Those constructions are used directly.

The existing dependencies supply the abstract adjoint-square and coefficient comparison
theorems, but do not directly state the equality for these particular native derived mates,
nor the geometric native proper-base-change result after affine localization. The two
new statements isolate exactly those steps. In particular, an objectwise existence theorem
in `WeilSheaf.ProperBaseChange` does not provide the natural transformation needed here.

Edge cases checked against the constructions and split statements: identity squares,
zero complexes, empty schemes, rank-zero local models, and nonseparated bases. The mate
comparison has no properness, Cartesian, boundedness or separatedness hypothesis; the
geometric theorem has no Frobenius datum and keeps the original relative properness and
qcqs/lft base hypotheses. No absolute separatedness is introduced.

## New nodes

`lem-sf-native-base-change-forget-comparison` realizes steps 1--4 of the original argument.
It states an equality of the actual forgotten morphism with the geometric mate conjugated
by explicitly defined comparisons. It proves no invertibility and applies to arbitrary
commutative squares and unbounded objects.

`lem-sf-geometric-native-proper-base-change` realizes steps 5--7 and the geometric part of
step 8. It concerns all bounded constructible native geometric adic inputs without a Weil
structure. Its proof follows the same separated affine charts, finite-span coefficient
comparison, rational proper base change, and open descent as the original plan.

No existing interface was changed, so no change record or consumer adaptation is required.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
