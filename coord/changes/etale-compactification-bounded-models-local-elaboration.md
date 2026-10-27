# AlgebraicGeometry.Etale.etaleCompactification_bounded_models

## Reason

Complete the theorem and repair the return at `e1c06963b` by reusing existing
proved private helpers. New local elaboration commands are conservatively treated
as an interface change by preflight. No existing signature, public import or
definition body changes, and no global attribute or instance is introduced.

## Old

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale
```

The existing theorem ended with `:= by sorry`. The canonical comparison definition
is preserved verbatim, including its body.

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Sheaf.instHasColimitsOfShape
  Functor.preservesZeroMorphisms_of_additive

attribute [local irreducible] lowerStar upperStar Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorUnitQ
```

These local priorities select existing instances and prevent expansion of scheme
and derived functors. The theorem has a complete proof, with private proved
`normalization_complex`, `comparison_cancel` and `acyclicComparison_naturality` helpers.

The returned duplicate `exact_factor_Q` and `unitQ_homotopy` declarations are removed.
Private proof imports use `import all` to access existing `comparison_complex_fac`
in `UnboundedEtaleCompactSupportComparisons` and `supportSheafIso` in
`EtaleSupportMapCompatibility`. Both imports pass the cycle check. Their existing
statements and proofs are unchanged. Only these helpers are used; no geometric
comparison theorem is invoked. The two unit definitions are identified by explicit
unfolding in a local proof. Naturality is proved generically to avoid expanding
scheme functors while rewriting. No new public declarations or modules are added. The repaired file compiles cleanly
with `lcompile.py` in 39.2 seconds, without warnings.

## Users

`tools/downstream.py` reports zero downstream modules and both public names only
in their own module. DAG parents retain their declarations and dependencies; no
consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCompactificationBoundedModels | K1 | Complete proof, private imports and proved helpers, local elaboration settings. |

## Status

landed 20261024T015144-L-2331094 2026-10-24 (merge of deliver/K1/Sheaf.AlgebraicGeometry.EtaleCompactificationBoundedModels)
