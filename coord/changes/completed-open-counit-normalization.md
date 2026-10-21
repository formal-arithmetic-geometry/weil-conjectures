# AlgebraicGeometry.Scheme.cbcDatumOrdinaryTransport_exists and AlgebraicGeometry.Scheme.cbcDatumTowerTransport_exists

## Reason

The existing normalization formulas repeated the same expanded morphism equation
inside the predicates passed to classical choice. A standalone reflexivity check
for the tower transport against its chosen witness spent about 29 seconds in the
kernel. Name the generic normalization condition and use that same condition in
both the universal comparison and the constant-square transport argument.

The named condition unfolds to the original equations, with the same quantified
complexes and the same counits. Exactness is supplied by the existing public
`towerModulePull_exact` theorem; it adds no hypothesis to either existence theorem.
The chosen ordinary and tower isomorphisms are still determined by the same unique
normalization. All six existing public construction bodies are verbatim.

The item compiled in 36.0 seconds and 38.6 seconds. All 19 checked consumers
compiled. An original-formula compatibility probe compiled by applying the
refactored theorems directly to their verbatim original statements.

## Old

```lean
theorem cbcDatumOrdinaryTransport_exists :
    ∃! e : completedOrdinaryPullback h d ≅ d.pull h,
      ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
              (d.integralRingIso h)).mapDerivedCategoryFactors.hom.app P =
          completedOrdinaryPullbackComplexCounit h d P ≫
            DerivedCategory.Q.map
              (eqToIso (cbcDatumModulePullComplex_eq d h P)).hom

theorem cbcDatumTowerTransport_exists :
    ∃! e : completedTowerPullback h d ≅ d.towerPull h,
      ∀ P : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (d.towerModulePull h).mapDerivedCategoryFactors.hom.app P =
          completedTowerPullbackComplexCounit h d P ≫
            DerivedCategory.Q.map
              (eqToIso (cbcDatumTowerPullComplex_eq d h P)).hom
```

## New

```lean
def CategoryTheory.Functor.ExactDerivedCounitNormalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [hLim : PreservesFiniteLimits G] [hColim : PreservesFiniteColimits G]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hp : ∀ P : CochainComplex C ℤ, (F.mapHomologicalComplex (.up ℤ)).obj P =
      (G.mapHomologicalComplex (.up ℤ)).obj P)
    (e : L ≅ G.mapDerivedCategory) : Prop :=
  ∀ P, e.hom.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategoryFactors.hom.app P =
    ε P ≫ DerivedCategory.Q.map (eqToIso (hp P)).hom

theorem cbcDatumOrdinaryTransport_exists :
    ∃! e : completedOrdinaryPullback h d ≅ d.pull h,
      ExactDerivedCounitNormalization (completedModulePullback h d)
        (proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
        (d.integralRingIso h)) (completedOrdinaryPullback h d)
        (completedOrdinaryPullbackComplexCounit h d)
        (cbcDatumModulePullComplex_eq d h) e

theorem cbcDatumTowerTransport_exists :
    ∃! e : completedTowerPullback h d ≅ d.towerPull h,
      ExactDerivedCounitNormalization
        (hLim := (d.towerModulePull_exact h).1)
        (hColim := (d.towerModulePull_exact h).2)
        (completedTowerModulePullback h d)
        (d.towerModulePull h) (completedTowerPullback h d)
        (completedTowerPullbackComplexCounit h d)
        (cbcDatumTowerPullComplex_eq d h) e
```

## Users

`tools/downstream.py --uses` finds only the item itself for either changed theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedOpenExchangeTransport | G5 | The choice predicates and the generic comparison share the named normalization; the original equations follow by unfolding it. |

## Status

landed 20261021T233720-L-853080 2026-10-21 (merge of deliver/G5/Sheaf.Paper.CompletedOpenExchangeTransport)
