# DiagonalCompletedReduction, diagonalSourceLimitMap, diagonalTargetLimitMap, diagonalTower_directImage, diagonalTower_limit

## Reason

The full file exceeded 60 seconds, mostly in kernel comparisons of repeated concrete
sheaf/derived-category expressions in the final proposition. Generic definitions now
share those structures and compositions. A local `HasLimit` instance directly projects
from `HasLimitsOfShape`, avoiding repeated site-limit inference. The complete four-proof
file compiled in 58.8 seconds with cached concrete tower limits and default
asynchronous elaboration. The identical generic interfaces were also checked by
compiling the unchanged `DiagonalTowerTraceLimit` consumer in 50.1 seconds.

`DiagonalCompletedReductionData` has exactly the old reduction record fields over an
arbitrary abelian category; `DiagonalCompletedReduction` specializes it to the original
completed category. Both endpoint maps retain their original signatures and compositions.
The two unfinished theorems retain every original binder. Their conclusions unfold to
precisely the original existential binders, conjunctions, normalization equations,
completeness tests and unique lift. No assertion is dropped or weakened. In particular,
`DiagonalLimitDataSpec` retains the original integral boundary and its derived map;
`diagonalCompleteDataAssertion` retains all finite quotient-unit equations.

No Challenge declaration or adopted source module changes. Because this is a definition
and statement-presentation change, targets whose definitions use it require the usual
independent meaning review. No new hole is introduced.

## Old

```lean
structure DiagonalCompletedReduction (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ X)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ X)] where
  derived : DiagonalDerivedReduction ℓ (𝟭 (DiagonalCompleted ℓ X))
  unit : ∀ n : ℕ, 𝟭 (DerivedCategory (DiagonalCompleted ℓ X)) ⟶
    derived.T ⋙ ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ X)).obj (op n)).mapDerivedCategory
  normalization : ∀ (P : CochainComplex (DiagonalCompleted ℓ X) ℤ) (n : ℕ),
    (unit n).app (DerivedCategory.Q.obj P) ≫
      ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ X)).obj (op n)).mapDerivedCategory.map
        (derived.ε.app P) ≫
      ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ X)).obj (op n)).mapDerivedCategoryFactors.hom.app
        ((derived.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (derived.ordinary.π n) (.up ℤ)).app P)
```

```lean
def diagonalSourceLimitMap (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y))) :
    (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj (diagonalCompletedDomain ℓ Y) ⟶
      L.R.obj (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))) :=
  ((diagonalCompletedRestriction ℓ (diagonalSurface Y)).mapDerivedCategorySingleFunctor 0).hom.app
      (diagonalCompletedSource ℓ Y) ≫
    (DerivedCategory.singleFunctor _ 0).map s.hom ≫
    diagonalOrdinaryRlim L (D.ordinary.E.obj (diagonalIntegralSource Y)) ≫
    L.R.map a.inv
```

```lean
def diagonalTargetLimitMap (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H) :
    (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj (diagonalCompletedCodomain ℓ Y) ⟶
      L.R.obj (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
        (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)) :=
  ((diagonalCompletedUnderlying ℓ (diagonalSurface Y)).commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj (Scheme.purTwistZlModule (diagonalSurface Y) ℓ)) ≫
    (shiftFunctor _ (2 : ℤ)).map
      (((diagonalCompletedRestriction ℓ (diagonalSurface Y)).mapDerivedCategorySingleFunctor
          0).hom.app (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≫
        (DerivedCategory.singleFunctor _ 0).map t.hom ≫ diagonalOrdinaryRlim L H) ≫
    (L.R.commShiftIso (2 : ℤ)).inv.app ((DerivedCategory.singleFunctor _ 0).obj H) ≫
    L.R.map b.inv
```

```lean
theorem diagonalTower_directImage (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ Y)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ Y)] :
    ∃ (LX : DiagonalRlim (DiagonalMod ℓ X)) (LY : DiagonalRlim (DiagonalMod ℓ Y))
      (Rf : DiagonalRightDerived (lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))
      (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ
        (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)))
      (e : ∀ n : ℕ, Rt.R ⋙
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategory ≅
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ X)).obj (op n)).mapDerivedCategory ⋙ Rf.R)
      (c : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LY.R)
      (c₀ : (lim : DiagonalSystems ℓ X ⥤ DiagonalMod ℓ X) ⋙
          lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f ≅
        (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f) ⋙ lim),
      (∀ H : DiagonalSystems ℓ X,
        c₀.hom.app H = limit.post H
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)) ∧
      (∀ P : CochainComplex (DiagonalSystems ℓ X) ℤ,
        Rf.η.app (((lim : DiagonalSystems ℓ X ⥤ DiagonalMod ℓ X).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ Rf.R.map (LX.η.app P) ≫ c.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app P) ≫
          LY.η.app ((((Functor.whiskeringRight ℕᵒᵖ
            (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
              (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)).mapHomologicalComplex
                (.up ℤ)).obj P) ≫ LY.R.map (Rt.η.app P)) ∧
      (∀ (P : CochainComplex (DiagonalSystems ℓ X) ℤ), P.IsKInjective → ∀ n : ℕ,
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
          (e n).hom.app (DerivedCategory.Q.obj P) ≫
          Rf.R.map (((evaluation ℕᵒᵖ (DiagonalMod ℓ X)).obj
            (op n)).mapDerivedCategoryFactors.hom.app P) =
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
            (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)).mapHomologicalComplex
              (.up ℤ)).obj P) ≫ Rf.η.app (P.asFunctor.obj (op n))) ∧
      ∀ (M : DerivedCategory (DiagonalSystems ℓ X)) (n : ℕ),
        c.hom.app M ≫ (LY.projection n).app (Rt.R.obj M) ≫ (e n).hom.app M =
          Rf.R.map ((LX.projection n).app M)
```

```lean
theorem diagonalTower_limit (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
  ∃ (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y) ∧
    c.hom = a.inv ≫ D.T.map (diagonalIntegralBoundary Y).hom ≫ b.hom ∧
    (∀ n : ℕ,
      ∃ (s : (D.ordinary.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
          (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
            ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
              (diagonalImmersion Y)).obj
                (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
        (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
          (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
            (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y))),
        DiagonalSourceNormalization ℓ Y D.ordinary n s ∧
        HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
          (roots.hom.app (op n) ≫
            cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
              (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
              (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)) ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
            (op n))).comp (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) =
          (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1) (diagonalImmersion Y)
            (diagonalImmersion_cartier Y) (diagonalSurface_power_unit ℓ Y hY n)).mapExactFunctor
               (diagonalFiniteToPadic ℓ n (diagonalSurface Y))) ∧
    ∃ (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
      (M : DiagonalCompletedReduction ℓ (diagonalSurface Y))
      (s₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (diagonalCompletedSource ℓ Y) ≅
        limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H),
      (∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s₀.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y))) ∧
      HEq ((diagonalForget ℓ (diagonalSurface Y)).map t₀.hom)
        (preservesLimitIso (diagonalForget ℓ (diagonalSurface Y)) H ≪≫
          HasLimit.isoOfNatIso roots).inv ∧
      IsIso (diagonalSourceLimitMap ℓ Y D a L s₀) ∧
      IsIso (diagonalTargetLimitMap ℓ Y D H b L t₀) ∧
      (∀ P : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ diagonalCompletedDomain ℓ Y)) ∧
      (∀ P : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ diagonalCompletedCodomain ℓ Y)) ∧
      (∃! δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y,
        (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map δ ≫
          diagonalTargetLimitMap ℓ Y D H b L t₀ =
          diagonalSourceLimitMap ℓ Y D a L s₀ ≫
            L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)) ∧
      ∀ (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y),
        (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map δ ≫
          diagonalTargetLimitMap ℓ Y D H b L t₀ =
          diagonalSourceLimitMap ℓ Y D a L s₀ ≫
            L.R.map (D.T.map (diagonalIntegralBoundary Y).hom) →
        ∀ n : ℕ,
          ∃ (s : (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
              ((M.derived.T ⋙ ((evaluation ℕᵒᵖ
                (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory).obj
                  (diagonalCompletedDomain ℓ Y)) ≅
              (((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
                (op n)).mapDerivedCategory).obj
                (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))))
            (t : (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
              ((M.derived.T ⋙ ((evaluation ℕᵒᵖ
                (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory).obj
                  (diagonalCompletedCodomain ℓ Y)) ≅
              (((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
                (op n)).mapDerivedCategory).obj
                (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
                  (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧))),
            (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map
                ((M.unit n).app (diagonalCompletedDomain ℓ Y)) ≫ s.hom =
              diagonalSourceLimitMap ℓ Y D a L s₀ ≫ (L.projection n).app
                (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))) ∧
            (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map
                ((M.unit n).app (diagonalCompletedCodomain ℓ Y)) ≫ t.hom =
              diagonalTargetLimitMap ℓ Y D H b L t₀ ≫ (L.projection n).app
                (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
                  (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)) ∧
            (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map
                ((M.derived.T ⋙ ((evaluation ℕᵒᵖ
                  (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory).map
                    δ) =
              s.hom ≫ (((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
                (op n)).mapDerivedCategory).map (D.T.map (diagonalIntegralBoundary Y).hom) ≫
                  t.inv
```

## New

```lean
structure DiagonalCompletedReductionData
    (ℓ : ℕ) (A : Type a) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] where
  derived : DiagonalDerivedReduction ℓ (𝟭 A)
  unit : ∀ n : ℕ, 𝟭 (DerivedCategory A) ⟶
    derived.T ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
  normalization : ∀ (P : CochainComplex A ℤ) (n : ℕ),
    (unit n).app (DerivedCategory.Q.obj P) ≫
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map
        (derived.ε.app P) ≫
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app
        ((derived.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (derived.ordinary.π n) (.up ℤ)).app P)
```

```lean
def diagonalSingleLimitComparison
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DiagonalRlim B) (P : A) (H : ℕᵒᵖ ⥤ B) (K : DerivedCategory (ℕᵒᵖ ⥤ B))
    (s : F.obj P ≅ limit H) (a : K ≅ (DerivedCategory.singleFunctor _ 0).obj H) :
    F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj P) ⟶ L.R.obj K :=
  (F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
    (DerivedCategory.singleFunctor _ 0).map s.hom ≫ diagonalOrdinaryRlim L H ≫ L.R.map a.inv
```

```lean
def diagonalShiftedSingleLimitComparison
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DiagonalRlim B) (P : A) (H : ℕᵒᵖ ⥤ B) (K : DerivedCategory (ℕᵒᵖ ⥤ B))
    (s : F.obj P ≅ limit H) (a : K ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor _ 0).obj P)⟦(2 : ℤ)⟧) ⟶
      L.R.obj K :=
  (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj P) ≫
    (shiftFunctor _ (2 : ℤ)).map
      ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
        (DerivedCategory.singleFunctor _ 0).map s.hom ≫ diagonalOrdinaryRlim L H) ≫
    (L.R.commShiftIso (2 : ℤ)).inv.app ((DerivedCategory.singleFunctor _ 0).obj H) ≫
    L.R.map a.inv
```

```lean
def diagonalExactFunctorExtImage
    {A : Type a} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {B : Type b} [Category.{u} B] [Abelian B] [HasExt.{w} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S U : A} {n : ℕ} (δ : Ext S U n) : Ext (F.obj S) (F.obj U) n :=
  δ.mapExactFunctor F
```

```lean
def diagonalDirectImageAssertion
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] : Prop :=
    ∃ (LX : DiagonalRlim A) (LY : DiagonalRlim B)
      (Rf : DiagonalRightDerived (F))
      (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ
        A B).obj
          (F)))
      (e : ∀ n : ℕ, Rt.R ⋙
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory ≅
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ Rf.R)
      (c : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LY.R)
      (c₀ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙
          F ≅
        (Functor.whiskeringRight ℕᵒᵖ A B).obj
          (F) ⋙ lim),
      (∀ H : (ℕᵒᵖ ⥤ A),
        c₀.hom.app H = limit.post H
          (F)) ∧
      (∀ P : CochainComplex ((ℕᵒᵖ ⥤ A)) ℤ,
        Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ Rf.R.map (LX.η.app P) ≫ c.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app P) ≫
          LY.η.app ((((Functor.whiskeringRight ℕᵒᵖ
            A B).obj
              (F)).mapHomologicalComplex
                (.up ℤ)).obj P) ≫ LY.R.map (Rt.η.app P)) ∧
      (∀ (P : CochainComplex ((ℕᵒᵖ ⥤ A)) ℤ), P.IsKInjective → ∀ n : ℕ,
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
          (e n).hom.app (DerivedCategory.Q.obj P) ≫
          Rf.R.map (((evaluation ℕᵒᵖ A).obj
            (op n)).mapDerivedCategoryFactors.hom.app P) =
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj
            (F)).mapHomologicalComplex
              (.up ℤ)).obj P) ≫ Rf.η.app (P.asFunctor.obj (op n))) ∧
      ∀ (M : DerivedCategory ((ℕᵒᵖ ⥤ A))) (n : ℕ),
        c.hom.app M ≫ (LY.projection n).app (Rt.R.obj M) ≫ (e n).hom.app M =
          Rf.R.map ((LX.projection n).app M)
```

```lean
def diagonalRootLimitComparison (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (H : DiagonalSystems ℓ X)
    (roots : H ⋙ diagonalForget ℓ X ≅
      Scheme.proEtaleRootsOfUnityTower X ℓ (Fact.out : ℓ.Prime)) :
    (diagonalForget ℓ X).obj (limit H) ≅
      limit (Scheme.proEtaleRootsOfUnityTower X ℓ (Fact.out : ℓ.Prime)) :=
  (preservesLimitIso (diagonalForget ℓ X) H).trans
    (HasLimit.isoOfNatIso (F := H ⋙ diagonalForget ℓ X)
      (G := Scheme.proEtaleRootsOfUnityTower X ℓ (Fact.out : ℓ.Prime)) roots)
```

```lean
def diagonalFiniteCycleNormalization
    {A : Type a} [Category.{v} A] [Abelian A]
    [HasExt.{w} A] [HasExt.{w} (ℕᵒᵖ ⥤ A)]
    (S H : ℕᵒᵖ ⥤ A) (c : Ext.{w} S H 2)
    (P Q : ℕ → A)
    (sourceNorm : ∀ n : ℕ, (S.obj (op n) ≅ P n) → Prop)
    (targetNorm : ∀ n : ℕ, (H.obj (op n) ≅ Q n) → Prop)
    (finiteClass : ∀ n : ℕ, Ext.{w} (P n) (Q n) 2) : Prop :=
  ∀ n : ℕ, ∃ (s : S.obj (op n) ≅ P n) (t : H.obj (op n) ≅ Q n),
    sourceNorm n s ∧ targetNorm n t ∧
      (Ext.mk₀.{w} s.inv).comp
        ((c.mapExactFunctor ((evaluation ℕᵒᵖ A).obj (op n))).comp
          (Ext.mk₀.{w} t.hom) (add_zero 2)) (zero_add 2) = finiteClass n
```

```lean
def DiagonalArrowCompatibility
    {C : Type a} [Category.{v} C] [Preadditive C]
    {B : Type b} [Category.{u} B] [Preadditive B]
    {E : Type w} [Category.{v} E]
    (ℓ : ℕ) (F : C ⥤ B) (R : E ⥤ B)
    (Rn : ℕ → C ⥤ C) (En : ℕ → E ⥤ B)
    (unit : ∀ n, 𝟭 C ⟶ Rn n) (π : ∀ n, R ⟶ En n)
    (P Q : C) (K J : E) (f : K ⟶ J)
    (s : F.obj P ⟶ R.obj K) (t : F.obj Q ⟶ R.obj J) : Prop :=
  IsIso s ∧ IsIso t ∧
    (∀ V : C, IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ P)) ∧
    (∀ V : C, IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ Q)) ∧
    (∃! δ : P ⟶ Q, F.map δ ≫ t = s ≫ R.map f) ∧
    ∀ δ : P ⟶ Q, F.map δ ≫ t = s ≫ R.map f → ∀ n : ℕ,
      ∃ (a : F.obj ((Rn n).obj P) ≅ (En n).obj K)
        (b : F.obj ((Rn n).obj Q) ≅ (En n).obj J),
        F.map ((unit n).app P) ≫ a.hom = s ≫ (π n).app K ∧
        F.map ((unit n).app Q) ≫ b.hom = t ≫ (π n).app J ∧
        F.map ((Rn n).map δ) = a.hom ≫ (En n).map f ≫ b.inv
```

```lean
def diagonalCompleteDataAssertion
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ B]
    (ℓ : ℕ) (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P Q : A) (S H : ℕᵒᵖ ⥤ B) (K J : DerivedCategory (ℕᵒᵖ ⥤ B))
    (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor _ 0).obj S)
    (b : J ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (sourceNorm : (F.obj P ≅ limit S) → Prop)
    (targetNorm : (F.obj Q ≅ limit H) → Prop) : Prop :=
  ∃ (L : DiagonalRlim B) (M : DiagonalCompletedReductionData ℓ A)
    (s : F.obj P ≅ limit S) (t : F.obj Q ≅ limit H),
    sourceNorm s ∧ targetNorm t ∧
    DiagonalArrowCompatibility ℓ F.mapDerivedCategory L.R
      (fun n ↦ M.derived.T ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory)
      (fun n ↦ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory)
      M.unit L.projection ((DerivedCategory.singleFunctor _ 0).obj P)
      (((DerivedCategory.singleFunctor _ 0).obj Q)⟦(2 : ℤ)⟧) K J f
      (diagonalSingleLimitComparison F L P S K s a)
      (diagonalShiftedSingleLimitComparison F L Q H J t b)
```

```lean
def DiagonalLimitDataSpec
    (ℓ : ℕ) {A : Type a} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {B : Type b} [Category.{u} B] [Abelian B]
    {C : Type c} [Category.{vc} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ C)] [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ B]
    (L₀ : A ⥤ B) (D : DiagonalDerivedReduction ℓ L₀)
    (S U : A) (boundary : Ext S U 1)
    (F : C ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P Q : C) (root : (ℕᵒᵖ ⥤ B) → Type r)
    (finite : ∀ H : ℕᵒᵖ ⥤ B, root H → Ext (D.ordinary.E.obj S) H 2 → Prop)
    (sourceNorm : (F.obj P ≅ limit (D.ordinary.E.obj S)) → Prop)
    (targetNorm : ∀ H : ℕᵒᵖ ⥤ B, root H → (F.obj Q ≅ limit H) → Prop) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : root H)
    (a : D.T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S))
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj U)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj S) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ L₀ D S ∧
      c.hom = a.inv ≫ D.T.map boundary.hom ≫ b.hom ∧ finite H roots c ∧
      diagonalCompleteDataAssertion ℓ F P Q (D.ordinary.E.obj S) H _ _
        (D.T.map boundary.hom) a b sourceNorm (targetNorm H roots)
```

```lean
def DiagonalCompletedLimitSpec (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y))) :
    Prop :=
  DiagonalLimitDataSpec ℓ
    (diagonalScalarExtension ℓ (diagonalSurface Y)) D
    (diagonalIntegralSource Y) (diagonalComparisonUnits Y) (diagonalIntegralBoundary Y)
    (diagonalCompletedRestriction ℓ (diagonalSurface Y))
    (diagonalCompletedSource ℓ Y) (Scheme.purTwistZlModule (diagonalSurface Y) ℓ)
    (fun H : DiagonalSystems ℓ (diagonalSurface Y) ↦
      H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
        Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (fun (H : DiagonalSystems ℓ (diagonalSurface Y)) roots c ↦
    diagonalFiniteCycleNormalization
      (A := DiagonalMod ℓ (diagonalSurface Y))
      (D.ordinary.E.obj (diagonalIntegralSource Y)) H c
      (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
          (diagonalImmersion Y)).obj
            (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
      (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)))
      (fun n s ↦ DiagonalSourceNormalization ℓ Y D.ordinary n s)
      (fun n t ↦ HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
        (roots.hom.app (op n) ≫
          cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
            (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
            (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)))
      (fun n ↦ diagonalExactFunctorExtImage (diagonalFiniteToPadic ℓ n (diagonalSurface Y))
        (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1)
          (diagonalImmersion Y) (diagonalImmersion_cartier Y)
          (diagonalSurface_power_unit ℓ Y hY n)))
    )
        (fun s₀ ↦ ∀ n : ℕ,
          diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
            (s₀.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
          (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
            (diagonalForget ℓ (diagonalSurface Y)).map
              ((D.ordinary.π n).app (diagonalIntegralSource Y)))
    (fun (H : DiagonalSystems ℓ (diagonalSurface Y))
        (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
          Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime)) ↦
        (fun (t₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
            (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅
              limit (J := ℕᵒᵖ) (C := DiagonalMod ℓ (diagonalSurface Y)) H) ↦
          HEq ((diagonalForget ℓ (diagonalSurface Y)).map t₀.hom)
          (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv))
```

```lean
abbrev DiagonalCompletedReduction (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ X)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ X)] :=
  DiagonalCompletedReductionData ℓ (DiagonalCompleted ℓ X)
```

```lean
def diagonalSourceLimitMap (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y))) :
    (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj (diagonalCompletedDomain ℓ Y) ⟶
      L.R.obj (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))) :=
  diagonalSingleLimitComparison (diagonalCompletedRestriction ℓ (diagonalSurface Y)) L
    (diagonalCompletedSource ℓ Y) _ _ s a
```

```lean
def diagonalTargetLimitMap (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H) :
    (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj (diagonalCompletedCodomain ℓ Y) ⟶
      L.R.obj (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
        (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)) :=
  diagonalShiftedSingleLimitComparison (diagonalCompletedRestriction ℓ (diagonalSurface Y)) L
    (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) _ _ t b
```

```lean
theorem diagonalTower_directImage (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ Y)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ Y)] :
    diagonalDirectImageAssertion
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)
```

```lean
theorem diagonalTower_limit (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
  DiagonalCompletedLimitSpec ℓ Y hY D
```

## Users

`tools/downstream.py --uses` finds the following direct declaration users among the
transitive import closure. The other transitive importers do not mention the changed
names. The supported source-library boundary is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalTowerLimit | V2 | Four original proofs filled; generic interfaces specialize to the original expressions. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Uses the reduction record and both endpoint maps; no mathematical change or adaptation needed. Original source compiled against these interfaces in 50.1 seconds. |

No other module mentions `DiagonalCompletedReduction`, `diagonalSourceLimitMap`,
`diagonalTargetLimitMap`, `diagonalTower_directImage` or `diagonalTower_limit`.
The domain, codomain, twist and underlying-functor declarations retain their original bodies.

## Status

landed 20261026T003014-L-138892 2026-10-26 (merge of deliver/V2/Sheaf.Paper.DiagonalTowerLimit)
