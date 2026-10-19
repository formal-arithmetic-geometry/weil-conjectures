## What changed

Proved `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible_rational_open_direct_image`
without changing its signature or any definition. The proof uses clause (4) of
`finiteCoefficientDescentTwoColimit` to identify the two constructibility predicates on the
source and target, applies the existing general
`CondensedRing.boundedConstructible_rightDerivedLowerStar_obj` separately to E and Qbar,
and converts back. The actual morphism in the over category has underlying map j.
The coefficient instances and base field are supplied explicitly to avoid expensive
instance and definitional-equality searches in the general direct-image application.
Added the ordinary proof import `Sheaf.Paper.FiniteCoefficientDescentTwoColimit`.
Updated the existing node's proof, proof dependencies and proof origin to this shorter route.
Public imports are unchanged. The proof docstring now describes the compiled shorter route. No unit statement or realized step is bypassed: the item's
unit record `sk-thm-restriction` has no realized attachment to this auxiliary node.
The two new proof-dependency paths were checked to have no route back to this item;
the added module also passed `import_direction.py may`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.constantModelBoundedConstructible_rational_open_direct_image`
(node `lem-sfb-rational-open-direct-image-constructible`). The final proof, with explicit instances and base field, compiled in 12.6 seconds.
This addresses fresh compile timeouts seen after an earlier successful dry run. No holes remain in the item;
no holes or nodes were added, and no statements were split off.
The proof intentionally uses existing stated library results, including the still-open
general direct-image theorem, as authorized by the stage-3 brief. This is a proof from
existing dependencies, not a claim that all transitive dependencies are sorry-free.

## No longer needed

Removed these ordinary proof imports (the complete list):

- `Sheaf.Paper.PadicIntegersInvertEll`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
- `Sheaf.Paper.CondensedFlatCoefficientCalculus`
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`
- `Sheaf.Paper.CompletedCondensedCoefficients`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CoefficientHeartTriangulated`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`
- `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage`
- `Sheaf.Paper.IntegralModels`
- `Sheaf.SixFunctors.ScalarSixPullback`

The original proof dependencies and maintainer tool-use approvals no longer directly
needed by this item's proof are:

- `det-cor-coefficient-heart-ii-triangulated`
- `det-prop-scalar-six-pullback`
- `det-prop-sfb-qlbar-colimit-x-invert-ell`
- `det-thm-sf-pf-adic-open`
- `lem-pc-right-derived-functor-triangulated`
- `lem-sfb-extend-scalars-preserves-homology`
- `lem-sfb-qlbar-flat`
- `lem-sfb-subfield-flat`
- `lem-weil-pbc-condensed-flat-coefficient-calculus`
- `lem-weil-pbc-condensed-qcqs-pushforward-continuity`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-qcqs-over-affine`
- `lem-weil-pbc-ring-sheaf-change-adjunction`
- `sk-def-sfb-coefficient-change`
- `sk-def-sfb-constructible`
- `sk-def-sfb-derived-tensor-hom`
- `sk-def-sfb-module-derived-pushpull`
- `sk-lem-integral-models`
- `sk-prop-sfb-cartesian-coefficients`
- `sk-prop-sfb-qlbar-colimit-x`

These were the explicit Noetherian/qcqs, integral-generator, localization telescope,
finite-free coefficient comparison and triangulated-generation route. The existing general
direct-image theorem already packages the needed preservation result, and the descent
equalities supply precisely the finite constant-model interface. This report prunes these
as direct dependencies of this item only; some remain transitive dependencies elsewhere.
All obsolete top-level `tool_uses` entries were withdrawn. No module is deleted.

## Where the brief, the DAG or earlier work was wrong

The DAG's eight-step plan is unnecessary for this item once the existing general
bounded-constructible direct-image theorem is combined with the now-proved predicate
equalities in finite coefficient descent. The finite constant-model input is converted
by an explicit equality, rather than assumed to imply the other predicate without proof.
No false statement, interface repair, consumer adaptation, or tool failure was found.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
