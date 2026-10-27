# AlgebraicGeometry.Scheme.cbcDerivedInverseExchange_exists

## Reason

The chosen derived inverse exchange repeats its large anonymous normalization predicate
in a uniqueness argument. Profiling the identity proof measured 41.4 seconds for kernel
checking that argument alone, and 91.8 seconds for the file. Give the existing predicate
a public name, exactly as the ordinary transport normalization is already named in
`CompletedOpenExchangeTransport`. This shares the condition in its existence theorem,
choice, and consumers. The generic `Functor.DerivedExchangeCounitNormalization` names the same counit
equation with its four module functors, resolving counits, underived exchange, and
representative predicate as arguments. The concrete
`cbcDerivedInverseExchangeNormalization` specializes it to exactly the previous
completed-module functors and K-flat predicate. Unfolding these two definitions
recovers the original condition verbatim; no
hypothesis, quantified complex, K-flat condition or equation is changed. The existing
choice definition and all other existing construction bodies remain verbatim.

A proved API lemma `cbcDerivedInverseExchange_eq` now applies uniqueness using
the named predicate. This lets the consumer keep the chosen exchange irreducible
and avoids opening the classical-choice implementation during its derivation.
It adds no hypothesis or axiom and is proved solely by the existing uniqueness.

The module was unclaimed in the current local claim records. No target meaning changes:
unfolding the named predicate recovers the original theorem type definitionally.

## Old

```lean
theorem cbcDerivedInverseExchange_exists :
    ∃! α : completedOrdinaryPullback gU d ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' ⟶
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ completedOrdinaryPullback g d,
      ∀ (P : CochainComplex ((pbcModules U (pbcAdicCompletion U d))) ℤ)
        (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P),
        α.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryPullback g d).map
            ((cbcOpenShriek d j sq.isOpenImmersion).mapDerivedCategoryFactors.hom.app P) ≫
          completedOrdinaryPullbackComplexCounit g d
            (((cbcOpenShriek d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj P) =
        (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
          (completedOrdinaryPullbackComplexCounit gU d P) ≫
          (cbcOpenShriek d j' sq.isOpenImmersion').mapDerivedCategoryFactors.hom.app
            (((completedModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            (((cbcUnderivedInverseExchange d sq).mapHomologicalComplex (.up ℤ)).app P)
```

## New

```lean
def CategoryTheory.Functor.DerivedExchangeCounitNormalization
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [HasDerivedCategory D] [HasDerivedCategory D']
    (F : C ⥤ C') (G : D ⥤ D') (J : C ⥤ D) (J' : C' ⥤ D')
    [F.Additive] [G.Additive] [J.Additive] [J'.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (LF : DerivedCategory C ⥤ DerivedCategory C')
    (LG : DerivedCategory D ⥤ DerivedCategory D')
    (ε : ∀ P : CochainComplex C ℤ, LF.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : ∀ P : CochainComplex D ℤ, LG.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (b : F ⋙ J' ⟶ J ⋙ G) (Good : CochainComplex C ℤ → Prop)
    (α : LF ⋙ J'.mapDerivedCategory ⟶ J.mapDerivedCategory ⋙ LG) : Prop :=
  ∀ P, Good P → α.app (DerivedCategory.Q.obj P) ≫
      LG.map (J.mapDerivedCategoryFactors.hom.app P) ≫
      δ ((J.mapHomologicalComplex (.up ℤ)).obj P) =
    J'.mapDerivedCategory.map (ε P) ≫
      J'.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b (.up ℤ)).app P)

def cbcDerivedInverseExchangeNormalization
    (α : completedOrdinaryPullback gU d ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' ⟶
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ completedOrdinaryPullback g d) : Prop :=
  Functor.DerivedExchangeCounitNormalization
    (completedModulePullback gU d) (completedModulePullback g d)
    (cbcOpenShriek d j sq.isOpenImmersion) (cbcOpenShriek d j' sq.isOpenImmersion')
    (completedOrdinaryPullback gU d) (completedOrdinaryPullback g d)
    (completedOrdinaryPullbackComplexCounit gU d)
    (completedOrdinaryPullbackComplexCounit g d) (cbcUnderivedInverseExchange d sq)
    (CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d)) α

theorem cbcDerivedInverseExchange_exists :
    ∃! α : completedOrdinaryPullback gU d ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' ⟶
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ completedOrdinaryPullback g d,
      cbcDerivedInverseExchangeNormalization d sq α
```

The proved uniqueness API is:

```lean
theorem cbcDerivedInverseExchange_eq
    (α : completedOrdinaryPullback gU d ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' ⟶
      cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ completedOrdinaryPullback g d)
    (hα : cbcDerivedInverseExchangeNormalization d sq α) :
    cbcDerivedInverseExchange d sq = α :=
  (cbcDerivedInverseExchange_exists d sq).unique
    (cbcDerivedInverseExchange_exists d sq).exists.choose_spec hα
```

## Users

`tools/downstream.py Sheaf.Paper.CompletedExtensionZeroComparison
--uses cbcDerivedInverseExchange_exists` reports one actual declaration-name consumer,
the defining module itself. A direct search of both library roots confirms this.
The new proof in the item also uses it. All transitive importers retain the same
public imports, normalization equation, uniquely specified exchange, and typeclass API;
no existing consumer requires an adaptation. The original formula is definitionally
the new predicate's expansion.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedExtensionZeroComparison | unclaimed | Name the unchanged choice predicate. |
| Sheaf.Paper.OrdinaryOpenExchangeIdentity | A3 | Use uniqueness with the shared predicate. |

## Status

landed 20261025T210727-L-3574966 2026-10-25 (merge of deliver/A3/Sheaf.Paper.OrdinaryOpenExchangeIdentity)
