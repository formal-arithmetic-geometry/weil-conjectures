# AlgebraicGeometry.ProEtale.QuotientChange.scalarSectionPushComparison

## Reason

Construct the same fixed pushforward comparison with its forward map expressed
as the typed geometric mate. The proved theorem scalarSectionPushMate_eq identifies
this map with the original comparison's forward map. The inverse is unchanged;
the two inverse laws follow by substituting this proved equality into the original
inverse laws. No data is chosen from existence or from an unproved theorem.
This keeps repeated kernel conversion of concrete derived constructions out of
later mate calculations. The original signature is preserved verbatim.

## Old

```lean
def scalarSectionPushComparison
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {U V : Scheme.{u}} (h : U ⟶ V) :
    F R h ⋙ ModuleRingedComparison.derivedFunctor R V ≅
      ModuleRingedComparison.derivedFunctor R U ⋙
        ModuleRingedComparison.derivedPushforward R h := by
  unfold F CondensedRing.moduleObjectDerivedPushforward
  exact ModuleRingedComparison.derivedPushComparison R h
```

## New

```lean
theorem scalarSectionPushMate_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {U V : Scheme.{u}} (h : U ⟶ V) :
    (mateEquiv (adj R h) (ModuleRingedComparison.derivedAdjunction R h)
      (TwoSquare.mk _ _ _ _ (scalarSectionPullComparison R h).inv)).natTrans =
        (by
          unfold F CondensedRing.moduleObjectDerivedPushforward
          exact (ModuleRingedComparison.derivedPushComparison R h).hom) := by
  have ht := ModuleRingedComparison.derivedMate R h
  unfold ModuleRingedComparison.normalizationInternalAdjunction
    ModuleRingedComparison.internalDerivedPullback
    ModuleRingedComparison.internalDerivedPushforward
    ModuleRingedComparison.comparisonSource at ht
  unfold adj scalarSectionPullComparison L F
    CondensedRing.moduleObjectDerivedPullback CondensedRing.moduleObjectDerivedPushforward
  exact ht

/-- The fixed pushforward realization with the named internal interface exposed.
Source: Stacks 07A6 (blueprint: lem-sfb-scalar-geometric-exchange-rectangle). -/
def scalarSectionPushComparison
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {U V : Scheme.{u}} (h : U ⟶ V) :
    F R h ⋙ ModuleRingedComparison.derivedFunctor R V ≅
      ModuleRingedComparison.derivedFunctor R U ⋙
        ModuleRingedComparison.derivedPushforward R h :=
  by
    let e : F R h ⋙ ModuleRingedComparison.derivedFunctor R V ≅
        ModuleRingedComparison.derivedFunctor R U ⋙
          ModuleRingedComparison.derivedPushforward R h := by
      unfold F CondensedRing.moduleObjectDerivedPushforward
      exact ModuleRingedComparison.derivedPushComparison R h
    have hm : (mateEquiv (adj R h) (ModuleRingedComparison.derivedAdjunction R h)
        (TwoSquare.mk _ _ _ _ (scalarSectionPullComparison R h).inv)).natTrans = e.hom := by
      exact scalarSectionPushMate_eq R h
    exact
      { hom := (mateEquiv (adj R h) (ModuleRingedComparison.derivedAdjunction R h)
          (TwoSquare.mk _ _ _ _ (scalarSectionPullComparison R h).inv)).natTrans
        inv := e.inv
        hom_inv_id := (congrArg (fun t ↦ t ≫ e.inv) hm).trans e.hom_inv_id
        inv_hom_id := (congrArg (fun t ↦ e.inv ≫ t) hm).trans e.inv_hom_id }
```

## Users

| module | holder | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarGeometricExchangeRectangle | J6 | Uses the definition and its mate equation in both realized routes. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | R9 | Two uses of the forward map in theorem statements; the map is unchanged by the proved equality. |
| Sheaf.Paper.InternalScalarMateProjection | J3 | Two uses of the forward map in data definitions; the map is unchanged by the proved equality. |

The read-only downstream.py --uses search reports exactly these three users.
No original signature, attribute or visibility changes. No consumer adaptation is
required: the functor types and canonical isomorphism remain the same. The new
proved helper belongs to the existing item node. It uses the already proved
geometric realization normalization, whose independent construction is retained.

## Status

landed 20261024T015051-L-2318376 2026-10-24 (merge of deliver/J6/Sheaf.Paper.ScalarGeometricExchangeRectangle)
