# AlgebraicGeometry.ProEtale.CondensedRing.integralConstructiblePullIso_comp

## Reason

Restore the assigned quarantined module under its original name. Its rework row records
reversion after a cluster restore, and its DAG attachment and two immediate parent nodes
still require the result. The archive already contains a complete proof, but the current
source library no longer exports the exact-right comparison equality used by comp_map_fac.
Use the existing canonical unit-factorization theorems instead. Local irreducibility
settings keep concrete derived functor definitions folded during proof elaboration.

## Old

The live item path is absent. The authoritative archive is
`quarantine/Sheaf/Paper/ContinuousIntegralPullComposition.lean`. Its public signature is:

```lean
theorem integralConstructiblePullIso_comp
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : integralConstructible ℓ E V) :
    (integralScalarConstructible ℓ E T).mapIso
        ((boundedConstructibleUpperStarComp (integralCoeff ℓ E) ℓ (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app K) ≪≫
      integralConstructiblePullIso ℓ E k h
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (j.asOver (Spec (.of k)))).obj K) ≪≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of k)))).mapIso
        (integralConstructiblePullIso ℓ E k j K) =
    integralConstructiblePullIso ℓ E k (h ≫ j) K ≪≫
      (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app
        ((integralScalarConstructible ℓ E V).obj K)
```

The archived comp_map_fac proof used
`Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived_eq`.
Its existing file-local elaboration option and local K-injective preservation instance
are retained.

## New

Restore the complete archived module at
`lean/Sheaf/Paper/ContinuousIntegralPullComposition.lean`, with its public signature,
public imports, definition bodies, helper names and visibility preserved. Only proof
code and whitespace are repaired. Add the proof-only import
`WeilConjectures.CategoryTheory.DerivedExactCompositionComparison`, and replace the
comp_map_fac proof by:

```lean
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app']
```

Omit the now-unused K-injective-resolution section assumption for D in comp_map_fac
and square_fac, and for C′ in square_comp. This assumption is unnecessary for the canonical exact-right comparison;
its removal changes no public signature and no consumer refers to this helper.

Add these file-local proof elaboration attributes inside the scheme namespace:

```lean
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.leftDerivedFunctorIsoMapDerivedCategory
```

These attributes do not change the definitions, their exported reducibility, or their
mathematical meaning. All new scope commands remain local to this module. The canonical size instance is
also registered locally:

```lean
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
```

The adjunction-transport unit equation is now instantiated at its fixed functor and
object and rearranged by `Iso.eq_inv_comp`. The final theorem uses `dsimp only`, focused
component rewrites and `convert` through the explicitly named inclusion definitions.
These are proof-body changes only. The private
comparison definition is the original explicit composite of isomorphisms, with no
choice from an unproved existence theorem. No target statement or definition changes;
no target semantic review is reopened. No sorry is added or moved.

## Users

`tools/downstream.py Sheaf.Paper.ContinuousIntegralPullComposition --allow-missing --names`
finds no live consumers. A separate import-graph traversal over both live roots and both
quarantine roots finds the nine archived transitive consumers below. The immediate
consumers are ContinuousIntegralExchangeTargetAdjunct and CondensedQbarPullbackCube.
The latter imports all and uses the preserved private derived_pull_comp and
bounded_comp_hom helpers. Both parent DAG nodes retain their original dependency.
All consumers keep the same mathematical statements and constructions; no adaptation
is needed or delivered. Holder information is a local coordination snapshot only.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Archived consumer; same interface and helper names, no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Archived consumer; same interface and helper names, no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Archived consumer; same interface and helper names, no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Archived consumer; same interface and helper names, no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Archived consumer; same interface and helper names, no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Archived consumer; same interface and helper names, no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Archived consumer; same interface and helper names, no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Archived consumer; same interface and helper names, no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Archived consumer; same interface and helper names, no adaptation. |

The complete restored module compiles cleanly in 45.3 seconds. The unchanged archived
direct consumer ContinuousIntegralExchangeTargetAdjunct compiles against it in
41.5 seconds, with only its pre-existing line-length warnings. The artifact axiom audit
still sees existing transitive sorry dependencies, documented in report.md; no direct
hole is introduced by the restoration or the repaired proofs.

## Status

landed 20261021T023319-L-2948459 2026-10-21 (merge of deliver/P4/Sheaf.Paper.ContinuousIntegralPullComposition)
