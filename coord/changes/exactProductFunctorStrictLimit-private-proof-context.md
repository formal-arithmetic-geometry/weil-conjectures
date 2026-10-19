# CategoryTheory.exactProductFunctorStrictLimit

## Reason

Preflight flags the new private-helper section, variables, omit commands and
elaboration options in the item as a possible change to visible context. This
record makes that change explicit for independent review. The existing theorem
signature, universes, visibility, docstring and public imports are identical.
No existing definition changes and no global instance or notation is registered.
Every added helper in the existing module is private and proved. The four new
public theorems are separately documented by their new DAG nodes.

## Old

The existing command context was:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uC vC r uD vD s wA wB
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
```

The public theorem signature was, verbatim:

```lean
theorem exactProductFunctorStrictLimit
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    {D : Type uD} [Category.{vD} D] (K : GrothendieckTopology D)
    [HasSheafify K AddCommGrpCat.{max uD vD s}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max uD vD s}]
    (S : Sheaf K RingCat.{max uD vD s})
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S)]
    (F : ringedSiteModules.{max uC vC r} R ⥤ ringedSiteModules.{max uD vD s} S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (_hphi : ∀ (M : ℕ → ringedSiteModules.{max uC vC r} R), IsIso (piComparison F M))
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤ DerivedCategory.{wA}
      (ringedSiteModules.{max uC vC r} R))
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ⥤ DerivedCategory.{wB}
      (ringedSiteModules.{max uD vD s} S))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙
        LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (ComplexShape.up ℤ)))
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uD vD s} S) ℤ) ⋙ DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙
        LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) (ComplexShape.up ℤ))) :
    ∃ (HA : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ⥤ CochainComplex
      (ringedSiteModules.{max uC vC r} R) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD
      vD s} S) ℤ ⥤ CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ)
      (hAobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ, HA.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ, HB.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), (HA.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (chiB : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) (p : ℤ), (HB.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
      (psi : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
      (kappa : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj X) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        X))
      (beta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (limit I.asFunctor) ≅ limit
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I).asFunctor)
      (lambda : LA ⋙ F.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB),
      -- The signed coordinates are pinned to the actual shifted cone, in both categories.
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), (chiA X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ ↦ V.X (p +
          1)) (hAobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) (p : ℤ), (chiB X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ ↦ V.X (p +
          1)) (hBobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      -- Roos maps are the product map on each signed coordinate.
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA Y p).hom = (chiA X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB Y p).hom = (chiB X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      -- K-injective normalization of the same thetaA and thetaB.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HA.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiA I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.{wA}.map iota) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HB.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiB I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.{wB}.map iota) ∧
      -- The canonical product map, and its two-summand version kappa.
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), (psi X).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k))
          n)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ) (n : ℕ),
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f (p + 1) =
          F.map ((chiA X p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f p =
          F.map ((chiA X p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p)) ∧
      -- This square is lambda = thetaB inverse, kappa, F(thetaA), in Lean order.
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapDerivedCategory).map (thetaA.hom.app X) ≫ F.mapDerivedCategoryFactors.hom.app (HA.obj
          X) ≫
            DerivedCategory.Q.{wB}.map (kappa X).hom =
          lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
              inferInstance⟩)).hom.app X) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X)) ∧
      -- Ordinary inverse limits are preserved, with the canonical projection normalization.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), (beta I).hom ≫
        limit.π ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
        ℤ)).obj I).asFunctor (op n) =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (limit.π I.asFunctor (op n))) ∧
      -- Every pair of K-injective resolutions computes this same lambda.
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (q : X ⟶ I) [QuasiIso q]
        [I.IsKInjective]
        (Jt : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) (r :
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I ⟶ Jt) [QuasiIso r] [Jt.IsKInjective],
        ∃ (dI : DerivedCategory.Q.{wA}.obj (limit I.asFunctor) ≅ LA.obj (DerivedCategory.Q.{wA}.obj
          X))
          (dJ : DerivedCategory.Q.{wB}.obj (limit Jt.asFunctor) ≅ LB.obj (DerivedCategory.Q.{wB}.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
            ℤ)).obj I))),
          dI.hom ≫ LA.map (DerivedCategory.Q.{wA}.map q) = etaA.app I ∧
          dJ.hom ≫ LB.map (DerivedCategory.Q.{wB}.map r) = etaB.app Jt ∧
          (F.mapDerivedCategory).map dI.hom ≫ lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) ≫
              LB.map (DerivedCategory.Q.{wB}.map ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) =
            F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
              DerivedCategory.Q.{wB}.map (beta I).hom ≫
              DerivedCategory.Q.{wB}.map (lim.map
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)) ≫ dJ.hom) ∧
      -- Only the coordinate-specified triangle maps occur in the triangle identities.
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        ∃ (p : HA.obj X ⟶ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n)))) (p' : HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          X) ⟶ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
          (delta : (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ⟶ (HA.obj X)⟦(1 : ℤ)⟧)
          (delta' : (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))) ⟶ (HB.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
            ℤ)).obj X))⟦(1 : ℤ)⟧),
          (∀ i : ℤ, p.f (i + 1) = (chiA X i).hom ≫ biprod.fst) ∧
          (∀ i : ℤ, p'.f (i + 1) = (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) i).hom ≫ biprod.fst) ∧
          (∀ i : ℤ, delta.f i ≫ ((HA.obj X).shiftFunctorObjXIso 1 i (i + 1) rfl).hom ≫
            (chiA X i).hom = -biprod.inr) ∧
          (∀ i : ℤ, delta'.f i ≫ ((HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).shiftFunctorObjXIso 1 i (i + 1)
            rfl).hom ≫
            (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
              ℤ)).obj X) i).hom = -biprod.inr) ∧
          lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) ≫
              thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X) ≫ DerivedCategory.Q.{wB}.map p' =
            (F.mapDerivedCategory).map (thetaA.hom.app X ≫ DerivedCategory.Q.{wA}.map p) ≫
              F.mapDerivedCategoryFactors.hom.app (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ≫
                DerivedCategory.Q.{wB}.map (psi X).hom ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map delta ≫
            (DerivedCategory.Q.{wA}.commShiftIso (1 : ℤ)).hom.app (HA.obj X) ≫
              (thetaA.inv.app X)⟦(1 : ℤ)⟧') ≫
              (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (LA.obj
                (DerivedCategory.Q.{wA}.obj X)) ≫
              (lambda.hom.app (DerivedCategory.Q.{wA}.obj X))⟦(1 : ℤ)⟧' ≫
              (LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X))⟦(1 : ℤ)⟧' =
            F.mapDerivedCategoryFactors.hom.app (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ≫
              DerivedCategory.Q.{wB}.map (psi X).hom ≫
              DerivedCategory.Q.{wB}.map delta' ≫ (DerivedCategory.Q.{wB}.commShiftIso (1 :
                ℤ)).hom.app (HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ≫
              (thetaB.inv.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X))⟦(1 : ℤ)⟧') ∧
      -- The strict augmentation maps are pinned by (gamma,0), not arbitrary derived arrows.
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (Q : CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) (gamma : ∀ n : ℕ, Q ⟶ X.asFunctor.obj (op n))
        (_hgamma : ∀ n : ℕ, gamma (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        ∃ (b : Q ⟶ HA.obj X) (b' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ⟶ HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          X)),
          (∀ i : ℤ, b.f (i + 1) ≫ (chiA X i).hom = biprod.lift ((Pi.lift gamma).f (i + 1)) 0) ∧
          (∀ i : ℤ, b'.f (i + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) i).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (gamma n))).f (i + 1)) 0) ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map b ≫ thetaA.inv.app X) ≫
              lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) =
            F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.{wB}.map b' ≫ thetaB.inv.app
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
              ℤ)).obj X)) 
```

## New

The public theorem has exactly the same signature displayed under Old.
Its proof now assembles the signed Roos comparison, chain comparison,
localization descent, resolution formula, and triangle and augmentation
compatibility. The added elaboration options are:

```lean
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

The generic product-preservation helpers have the following scoped context,
which ends before the original public declaration:

```lean
section
variable {A : Type*} {B : Type*} [Category* A] [Category* B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
omit [Abelian A] [Abelian B] in
-- private theorem natProducts
omit [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B] in
-- private theorem infiniteProducts
omit [Abelian B] [HasCountableProducts B] in
-- private theorem natProducts_preservesTowers
end
```

Additional private helpers prove signed-coordinate transport and normalized
Roos comparison. Local maxHeartbeats settings support elaboration of the
simultaneous universe-polymorphic cone comparisons. All added imports in the
existing module are proof-only. The original public-import list is retained.
The new modules' public declarations do not change existing statements or
register instances or attributes on existing declarations.

## Users

The source-only downstream audit found 264 transitive importers.
Its declaration-use scan found only the defining module. Every importer keeps
the same exported theorem and public imports. No consumer signature or target
meaning changes, and no consumer adaptation is needed. Holder information is a
snapshot of the available coordination records.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | F9 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | W9 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | R3 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | U3 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CompleteCompactSupportProetale | J3 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | Y7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Y9 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ExactProductFunctorStrictLimit | J1 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | F1 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | G1 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | N2 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | Y8 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | F7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | T6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | T7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.PuncturedDerivedCompletionSections | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | H2 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | S4 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | P2 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.RationalStalkExact | A7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | R3 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | Q8 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | P7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | R5 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | U2 | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Same theorem signature and public imports; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | B5 | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Same theorem signature and public imports; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | Y7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | P7 | Same theorem signature and public imports; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same theorem signature and public imports; no adaptation. |
| TargetsCheck | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same theorem signature and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same theorem signature and public imports; no adaptation. |

## Status

landed 20261019T112451-L-3942830 2026-10-19 (merge of deliver/J1/Sheaf.Paper.ExactProductFunctorStrictLimit)
