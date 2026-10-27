# CategoryTheory.exactProductFunctorStrictLimit

## Reason

The full existential conclusion is repeatedly specialized to concrete sheaf-module
categories by the open Roos comparison proof. This expands inherited abelian
structures and the complex limit instances during elaboration and kernel checks.
Name the existing conclusion as `StrictLimitAssertions`; the statement remains
definitionally equal to its previous expansion. The construction and every
normalization clause, including both triangle clauses, stay intact. The new
predicate contains no chosen data and no proof hole.

## Old

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
    StrictLimitAssertions F LA LB etaA etaB
```

`StrictLimitAssertions` is the verbatim previous conclusion abstracted over
its category arguments. This is a definition repair, not a weakening of the
statement. No target declaration changes. The main item additionally proves the
strict augmentation resolution normalization from this same existing theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.RoosConeCompositorDescent | not adapted | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | not adapted | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.Paper.CompletedOpenEndpointLimitTransport | not adapted | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | not adapted | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.Paper.ExactProductFunctorStrictLimit | unclaimed (previous J1 item landed) | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.Paper.FdScalarRoosComparisonIntertwining | not adapted | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.Paper.RingedOpenScalarLimitCoherence | not adapted | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.Paper.SfOpenRoosExtensionComparison | T4 | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | not adapted | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.SixFunctors.OpenQuotientCompletionUnitComparison | not adapted | Definitionally equal conclusion; existing binders and assertions retained. |
| Sheaf.SixFunctors.RoosAdjunctionUnitCoherence | not adapted | Definitionally equal conclusion; existing binders and assertions retained. |

These are the direct declaration users found with `rg`; the downstream module
closure also sees the definitionally equal type. Only the strict-limit module
and the assigned item are edited. Existing consumers need no source changes.

## Status

landed 20261025T003345-L-3232879 2026-10-25 (merge of deliver/T4/Sheaf.Paper.SfOpenRoosExtensionComparison)
