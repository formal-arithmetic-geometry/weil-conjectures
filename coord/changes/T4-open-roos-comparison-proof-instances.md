# WeilConjectures.SfOpenRoos.ComparisonAssertions

## Reason

Profiling the original specification reports repeated `HasLimit` searches for
complexes (about 0.22--0.28 seconds per occurrence). The prefix through this
specification took 33.5 seconds, with 16.6 seconds in typeclass inference; the
complete proof exceeded the unchanged 60-second compile limit. Cache the four shape-existence instances and the four corresponding
pointwise limit-existence families in the definition body. Every cached class is a proposition,
so proof irrelevance makes the resulting definition definitionally equal to the
original. No binder, universe, coordinate equation or assertion changes.

The proof also uses locally scoped reduction barriers on
`completedIntegralCoefficientSheafUnrestricted` and `extension`, to avoid
unfolding the completed inverse limit and sheafification composite during
inference. Neither underlying definition nor its exported reducibility changes.
Local backward-definitional-equality options likewise affect only elaboration.

## Old

```lean
def ComparisonAssertions (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ⋙
        DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex B ℤ) ⥤ CochainComplex B ℤ) ⋙
        DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB) : Prop :=
    ∃ (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
      (hAobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, HA.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, HB.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (HA.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
      (chiB : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (HB.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
      (psi : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦
          (M).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op n))))
      (kappa : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj M) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        M))
      (beta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (limit I.asFunctor) ≅
          limit
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        I).asFunctor)
      (lambda : LA ⋙ F.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _
        _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦
          inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB),
      -- The signed coordinates are pinned to the actual shifted cone, in both categories.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (chiA M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (A) ℤ ↦ V.X (p +
          1)) (hAobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (chiB M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (B) ℤ ↦ V.X (p +
          1)) (hBobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      -- Roos maps are the product map on each signed coordinate.
      (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : M ⟶ N) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA N p).hom = (chiA M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : M ⟶ N) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB N p).hom = (chiB M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      -- K-injective normalization of the same thetaA and thetaB.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HA.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiA I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.{wA}.map iota) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HB.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiB I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.{wB}.map iota) ∧
      -- The canonical product map, and its two-summand version kappa.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (psi M).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦
          M.asFunctor.obj (op k))
          n)) ∧
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ),
        (kappa M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f (p + 1) =
          F.map ((chiA M p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappa M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f p =
          F.map ((chiA M p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f p)) ∧
      -- This square is lambda = thetaB inverse, kappa, F(thetaA), in Lean order.
      (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapDerivedCategory).map (thetaA.hom.app M) ≫ F.mapDerivedCategoryFactors.hom.app (HA.obj
          M) ≫
            DerivedCategory.Q.{wB}.map (kappa M).hom =
          lambda.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
                _ _ _ ↦
              inferInstance⟩)).hom.app M) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ∧
      -- Ordinary inverse limits are preserved, with the canonical projection normalization.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (beta I).hom ≫
        limit.π ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
        ℤ)).obj I).asFunctor (op n) =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (limit.π I.asFunctor
          (op n))) ∧
      -- Every pair of K-injective resolutions computes this same lambda.
      (∀ (M I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : M ⟶ I) [QuasiIso q]
        [I.IsKInjective]
        (Jt : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (r :
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          I ⟶ Jt) [QuasiIso r] [Jt.IsKInjective],
        ∃ (dI : DerivedCategory.Q.{wA}.obj (limit I.asFunctor) ≅ LA.obj (DerivedCategory.Q.{wA}.obj
          M))
          (dJ : DerivedCategory.Q.{wB}.obj (limit Jt.asFunctor) ≅ LB.obj (DerivedCategory.Q.{wB}.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up
            ℤ)).obj I))),
          dI.hom ≫ LA.map (DerivedCategory.Q.{wA}.map q) = etaA.app I ∧
          dJ.hom ≫ LB.map (DerivedCategory.Q.{wB}.map r) = etaB.app Jt ∧
          (F.mapDerivedCategory).map dI.hom ≫ lambda.hom.app
            (DerivedCategory.Q.{wA}.obj M) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩)
                  (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app M) ≫
              LB.map (DerivedCategory.Q.{wB}.map ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) =
            F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
              DerivedCategory.Q.{wB}.map (beta I).hom ≫
              DerivedCategory.Q.{wB}.map (lim.map
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)) ≫ dJ.hom) ∧
      -- The strict augmentation maps are pinned by (gamma,0), not arbitrary derived arrows.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Q : CochainComplex
        (A) ℤ) (gamma : ∀ n : ℕ, Q ⟶ M.asFunctor.obj (op n))
        (_hgamma : ∀ n : ℕ, gamma (n + 1) ≫ M.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        ∃ (b : Q ⟶ HA.obj M) (b' : (F.mapHomologicalComplex (ComplexShape.up
          ℤ)).obj Q ⟶ HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          M)),
          (∀ i : ℤ, b.f (i + 1) ≫ (chiA M i).hom = biprod.lift ((Pi.lift gamma).f (i + 1)) 0) ∧
          (∀ i : ℤ, b'.f (i + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) i).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ (F.mapHomologicalComplex
              (ComplexShape.up ℤ)).map
              (gamma n))).f (i + 1)) 0) ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map b ≫
            thetaA.inv.app M) ≫
              lambda.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩)
                  (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app M) =
            F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.{wB}.map
              b' ≫ thetaB.inv.app
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up
              ℤ)).obj M) ∧
          -- The coordinate maps are the actual maps induced by the augmentations.
          (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
              (q : M ⟶ I) [QuasiIso q] [I.IsKInjective],
            ∃ (dI : DerivedCategory.Q.{wA}.obj (limit I.asFunctor) ≅
                LA.obj (DerivedCategory.Q.{wA}.obj M)) (a : Q ⟶ limit I.asFunctor),
              dI.hom ≫ LA.map (DerivedCategory.Q.{wA}.map q) = etaA.app I ∧
              (∀ n : ℕ, a ≫ limit.π I.asFunctor (op n) = gamma n ≫
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
              DerivedCategory.Q.{wA}.map b ≫ thetaA.inv.app M =
                DerivedCategory.Q.{wA}.map a ≫ dI.hom) ∧
          (∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
              (q : (((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ I)
              [QuasiIso q] [I.IsKInjective],
            ∃ (dI : DerivedCategory.Q.{wB}.obj (limit I.asFunctor) ≅
                LB.obj (DerivedCategory.Q.{wB}.obj
                  ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                    F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)))
              (a : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ⟶
                limit I.asFunctor),
              dI.hom ≫ LB.map (DerivedCategory.Q.{wB}.map q) = etaB.app I ∧
              (∀ n : ℕ, a ≫ limit.π I.asFunctor (op n) =
                (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (gamma n) ≫
                  (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
              DerivedCategory.Q.{wB}.map b' ≫ thetaB.inv.app
                ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                  F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
                DerivedCategory.Q.{wB}.map a ≫ dI.hom))
```

## New

```lean
def ComparisonAssertions (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ⋙
        DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex B ℤ) ⥤ CochainComplex B ℤ) ⋙
        DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB) : Prop :=
    letI : HasLimitsOfShape ℕᵒᵖ (CochainComplex A ℤ) := inferInstance
    letI : HasLimitsOfShape ℕᵒᵖ (CochainComplex B ℤ) := inferInstance
    letI : HasLimitsOfShape (Discrete ℕ) (CochainComplex A ℤ) := inferInstance
    letI : HasLimitsOfShape (Discrete ℕ) (CochainComplex B ℤ) := inferInstance
    letI : ∀ T : ℕᵒᵖ ⥤ CochainComplex A ℤ, HasLimit T := fun _ ↦ inferInstance
    letI : ∀ T : ℕᵒᵖ ⥤ CochainComplex B ℤ, HasLimit T := fun _ ↦ inferInstance
    letI : ∀ T : Discrete ℕ ⥤ CochainComplex A ℤ, HasLimit T := fun _ ↦ inferInstance
    letI : ∀ T : Discrete ℕ ⥤ CochainComplex B ℤ, HasLimit T := fun _ ↦ inferInstance
    ∃ (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
      (hAobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, HA.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, HB.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (HA.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
      (chiB : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (HB.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
      (psi : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦
          (M).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op n))))
      (kappa : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj M) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        M))
      (beta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (limit I.asFunctor) ≅
          limit
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        I).asFunctor)
      (lambda : LA ⋙ F.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _
        _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦
          inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB),
      -- The signed coordinates are pinned to the actual shifted cone, in both categories.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (chiA M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (A) ℤ ↦ V.X (p +
          1)) (hAobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (chiB M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (B) ℤ ↦ V.X (p +
          1)) (hBobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      -- Roos maps are the product map on each signed coordinate.
      (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : M ⟶ N) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA N p).hom = (chiA M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : M ⟶ N) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB N p).hom = (chiB M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      -- K-injective normalization of the same thetaA and thetaB.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HA.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiA I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.{wA}.map iota) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HB.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiB I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.{wB}.map iota) ∧
      -- The canonical product map, and its two-summand version kappa.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (psi M).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦
          M.asFunctor.obj (op k))
          n)) ∧
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ),
        (kappa M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f (p + 1) =
          F.map ((chiA M p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappa M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f p =
          F.map ((chiA M p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f p)) ∧
      -- This square is lambda = thetaB inverse, kappa, F(thetaA), in Lean order.
      (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapDerivedCategory).map (thetaA.hom.app M) ≫ F.mapDerivedCategoryFactors.hom.app (HA.obj
          M) ≫
            DerivedCategory.Q.{wB}.map (kappa M).hom =
          lambda.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
                _ _ _ ↦
              inferInstance⟩)).hom.app M) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ∧
      -- Ordinary inverse limits are preserved, with the canonical projection normalization.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (beta I).hom ≫
        limit.π ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
        ℤ)).obj I).asFunctor (op n) =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (limit.π I.asFunctor
          (op n))) ∧
      -- Every pair of K-injective resolutions computes this same lambda.
      (∀ (M I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : M ⟶ I) [QuasiIso q]
        [I.IsKInjective]
        (Jt : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (r :
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          I ⟶ Jt) [QuasiIso r] [Jt.IsKInjective],
        ∃ (dI : DerivedCategory.Q.{wA}.obj (limit I.asFunctor) ≅ LA.obj (DerivedCategory.Q.{wA}.obj
          M))
          (dJ : DerivedCategory.Q.{wB}.obj (limit Jt.asFunctor) ≅ LB.obj (DerivedCategory.Q.{wB}.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up
            ℤ)).obj I))),
          dI.hom ≫ LA.map (DerivedCategory.Q.{wA}.map q) = etaA.app I ∧
          dJ.hom ≫ LB.map (DerivedCategory.Q.{wB}.map r) = etaB.app Jt ∧
          (F.mapDerivedCategory).map dI.hom ≫ lambda.hom.app
            (DerivedCategory.Q.{wA}.obj M) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩)
                  (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app M) ≫
              LB.map (DerivedCategory.Q.{wB}.map ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) =
            F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
              DerivedCategory.Q.{wB}.map (beta I).hom ≫
              DerivedCategory.Q.{wB}.map (lim.map
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)) ≫ dJ.hom) ∧
      -- The strict augmentation maps are pinned by (gamma,0), not arbitrary derived arrows.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Q : CochainComplex
        (A) ℤ) (gamma : ∀ n : ℕ, Q ⟶ M.asFunctor.obj (op n))
        (_hgamma : ∀ n : ℕ, gamma (n + 1) ≫ M.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        ∃ (b : Q ⟶ HA.obj M) (b' : (F.mapHomologicalComplex (ComplexShape.up
          ℤ)).obj Q ⟶ HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          M)),
          (∀ i : ℤ, b.f (i + 1) ≫ (chiA M i).hom = biprod.lift ((Pi.lift gamma).f (i + 1)) 0) ∧
          (∀ i : ℤ, b'.f (i + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) i).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ (F.mapHomologicalComplex
              (ComplexShape.up ℤ)).map
              (gamma n))).f (i + 1)) 0) ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map b ≫
            thetaA.inv.app M) ≫
              lambda.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩)
                  (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app M) =
            F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.{wB}.map
              b' ≫ thetaB.inv.app
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up
              ℤ)).obj M) ∧
          -- The coordinate maps are the actual maps induced by the augmentations.
          (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
              (q : M ⟶ I) [QuasiIso q] [I.IsKInjective],
            ∃ (dI : DerivedCategory.Q.{wA}.obj (limit I.asFunctor) ≅
                LA.obj (DerivedCategory.Q.{wA}.obj M)) (a : Q ⟶ limit I.asFunctor),
              dI.hom ≫ LA.map (DerivedCategory.Q.{wA}.map q) = etaA.app I ∧
              (∀ n : ℕ, a ≫ limit.π I.asFunctor (op n) = gamma n ≫
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
              DerivedCategory.Q.{wA}.map b ≫ thetaA.inv.app M =
                DerivedCategory.Q.{wA}.map a ≫ dI.hom) ∧
          (∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
              (q : (((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ I)
              [QuasiIso q] [I.IsKInjective],
            ∃ (dI : DerivedCategory.Q.{wB}.obj (limit I.asFunctor) ≅
                LB.obj (DerivedCategory.Q.{wB}.obj
                  ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                    F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)))
              (a : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ⟶
                limit I.asFunctor),
              dI.hom ≫ LB.map (DerivedCategory.Q.{wB}.map q) = etaB.app I ∧
              (∀ n : ℕ, a ≫ limit.π I.asFunctor (op n) =
                (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (gamma n) ≫
                  (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
              DerivedCategory.Q.{wB}.map b' ≫ thetaB.inv.app
                ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                  F).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
                DerivedCategory.Q.{wB}.map a ≫ dI.hom))
```

## Users

`tools/downstream.py Sheaf.Paper.SfOpenRoosExtensionComparison` reports the two
consumers below. With `--uses ComparisonAssertions`, it reports only this item's
two internal occurrences. All existing public signatures stay identical. The
cached instances are proofs, and the original and new predicates are
definitionally equal; no consumer adaptation or target re-review is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfOpenRoosExtensionComparison | T4 | Cached proof instances and complete theorem proofs. |
| Sheaf.Paper.SfOpenRoosRestrictionUnit | unclaimed | No adaptation; unchanged public interface. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed | No adaptation; unchanged public interface. |

## Status

landed 20261025T003345-L-3232879 2026-10-25 (merge of deliver/T4/Sheaf.Paper.SfOpenRoosExtensionComparison)
