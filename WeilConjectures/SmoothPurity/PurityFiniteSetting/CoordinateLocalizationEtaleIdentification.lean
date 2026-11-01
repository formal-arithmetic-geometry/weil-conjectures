/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomCocycleNormalization

/-! # Normalized étale supported-Hom identification for the coordinate pair

Source: Milne, Lectures on Etale Cohomology, Section 9, Example 9.5 and the
proof of Theorem 9.4 (blueprint: lem-pur-coordinate-localization-splice-support-class-etale).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The coordinate étale support pair. -/
private noncomputable abbrev coordinateEtalePair (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  etaleSupportHomPair P (zeroSection T)

private noncomputable abbrev coordinateEtaleCycle (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex.Plus
      (Sheaf (Line T).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ) :=
  (((coordinateEtalePair P T).sections.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    I.obj).cycles a

private noncomputable abbrev coordinateEtaleClass (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex.Plus
      (Sheaf (Line T).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ) (x : coordinateEtaleCycle P T I a) :=
  (Sheaf.supportSequenceModelIso (Line T).smallEtaleTopology
    (ModuleCat.{u + 1} P.Coefficient) (coordinateEtalePair P T).sections I
    (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a).hom
    ((((coordinateEtalePair P T).sections.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      I.obj).homologyπ a x)

/-- The prescribed and normalized supported-Hom identifications agree on every
injective representative and every supported cocycle.

Source: Milne, Lectures on Etale Cohomology, Section 9, Example 9.5 and the
injective-resolution proof of Theorem 9.4.
Proof: use the evaluation-at-one normalization to identify the unique map
representing a supported cycle, then apply the two cocycle formulas. The
localized roof and the identity resolution comparison are preserved by the
canonical quotient maps.
This is the injective-model step of the module's blueprint node.
-/
private theorem coordinateLocalization_etale_identification_on_injective
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : CoordinateBoundaryModel P T)
    (N : SupportedHomCocycleNormalization
      (coordinateEtalePair P T).topology P.Coefficient
      (coordinateEtalePair P T).isTerminal
      (coordinateEtalePair P T).restriction
      (coordinateEtalePair P T).supported
      (coordinateEtalePair P T).constantRestriction) :
    ∀ (I : CochainComplex.Plus
      (Sheaf (Line T).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
      (x : coordinateEtaleCycle P T I a),
      M.chiEtale.chi (DerivedCategory.Plus.Q.obj I) a
          (coordinateEtaleClass P T I a x) =
        N.chi (DerivedCategory.Plus.Q.obj I) a
          (coordinateEtaleClass P T I a x) := by
  intro I hi a x
  obtain ⟨f, ⟨hθ, hf, hχ⟩, _⟩ := N.cocycle I I (𝟙 I) a x
  have hid : supportedHomResolutionIso (coordinateEtalePair P T).topology P.Coefficient
      I I (𝟙 I) = Iso.refl _ := by
    apply Iso.ext
    apply DerivedCategory.Plus.ι.map_injective
    change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) = _
    rw [Functor.map_preimage]
    simp
    rfl
  rw [hid] at hχ
  have hqi : (DerivedCategory.quotientCompQhIso
      (Sheaf (Line T).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))).inv.app
        I.obj = 𝟙 _ := rfl
  rw [hqi] at hχ
  dsimp only [Iso.refl_inv] at hχ
  repeat first
    | erw [CategoryTheory.Functor.map_id] at hχ
    | erw [Category.comp_id] at hχ
  have heval :
      kernel.ι ((I.obj.X a).obj.map (coordinateEtalePair P T).restriction.op)
          (((coordinateEtalePair P T).complex I).iCycles a x) =
        ((constantSheafAdj (coordinateEtalePair P T).topology
          (ModuleCat.{u + 1} P.Coefficient) (coordinateEtalePair P T).isTerminal).homEquiv
          _ _ ((coordinateEtalePair P T).constantRestriction ≫ f)) 1 := by
    rw [← hθ]
    exact N.evaluation _ f
  have hm := M.chiEtale.normalization I a f hf x heval
  have hqh : (DerivedCategory.quotientCompQhIso
      (Sheaf (Line T).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))).hom.app
        I.obj = 𝟙 _ := rfl
  change _ = supportedHomLocalizedCocycle I.obj a f hf ≫
    ((DerivedCategory.quotientCompQhIso _).hom.app I.obj)⟦a⟧' at hm
  rw [hqh] at hm
  erw [(shiftFunctor _ a).map_id, Category.comp_id] at hm
  exact hm.trans hχ.symm

/-- Extend equality of the coordinate supported-Hom maps from injective models
to every object of the bounded-below derived category.

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4.
Proof: choose a bounded-below injective model, lift supported cohomology
classes to cycles, and use naturality along the model isomorphism. The two
inverse comparison maps cancel, so the injective-model equality determines the
map on every object and in every integer degree.
This is the naturality step of the module's blueprint node.
-/
private theorem coordinateLocalization_etale_identification_extend
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : CoordinateBoundaryModel P T)
    (N : SupportedHomCocycleNormalization
      (coordinateEtalePair P T).topology P.Coefficient
      (coordinateEtalePair P T).isTerminal
      (coordinateEtalePair P T).restriction
      (coordinateEtalePair P T).supported
      (coordinateEtalePair P T).constantRestriction)
    (hI : ∀ (I : CochainComplex.Plus
      (Sheaf (Line T).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
      (x : coordinateEtaleCycle P T I a),
      M.chiEtale.chi (DerivedCategory.Plus.Q.obj I) a
          (coordinateEtaleClass P T I a x) =
        N.chi (DerivedCategory.Plus.Q.obj I) a
          (coordinateEtaleClass P T I a x)) :
    ∀ (K : DerivedCategory.Plus
      (Sheaf (Line T).smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ),
      M.chiEtale.chi K a = N.chi K a := by
  classical
  have hinj (I : CochainComplex.Plus
      (Sheaf (Line T).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (hi : ∀ n : ℤ, Injective (I.obj.X n)) (a : ℤ)
      (s : (coordinateEtalePair P T).group (DerivedCategory.Plus.Q.obj I) a) :
      M.chiEtale.chi (DerivedCategory.Plus.Q.obj I) a s =
        N.chi (DerivedCategory.Plus.Q.obj I) a s := by
    let _ := hi
    let E := Sheaf.supportSequenceModelIso (Line T).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient) (coordinateEtalePair P T).sections I
      (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective
      (((coordinateEtalePair P T).complex I).homologyπ a)).mp inferInstance (E.inv s)
    have hclass : coordinateEtaleClass P T I a x = s := by
      change E.hom (((coordinateEtalePair P T).complex I).homologyπ a x) = s
      rw [hx]
      exact ConcreteCategory.congr_hom E.inv_hom_id s
    simpa only [hclass] using hI I a x
  intro K a
  obtain ⟨m, hm⟩ := K.2
  let : K.IsGE m := (K.isGE_ι_obj_iff m).1 hm
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K m
  let I := (InjectiveObject.ι
    (Sheaf (Line T).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))).mapCochainComplexPlus.obj L
  have hi (n : ℤ) : Injective (I.obj.X n) := (L.obj.X n).2
  apply AddEquiv.ext
  intro s
  apply (cancel_mono ((DerivedCategory.Plus.ι.map e.inv)⟦a⟧')).mp
  rw [← M.chiEtale.naturality _ _ e.inv a s, ← N.naturality _ _ e.inv a s]
  exact hinj I hi a _

private theorem constantSheafAdj_evaluation
    {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u + 1} A)] {T : C}
    (hT : IsTerminal T) (M : Sheaf J (ModuleCat.{u + 1} A))
    (f : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ M) :
    (constantSheafAdj J (ModuleCat.{u + 1} A) hT).homEquiv _ _ f =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A))).app (op T) ≫
        f.hom.app (op T) := by
  rfl

private theorem constantSheafDirectImage_evaluation
    {A : Type (u + 1)} [CommRing A]
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
    [HasSheafify J (ModuleCat.{u + 1} A)] [HasSheafify J' (ModuleCat.{u + 1} A)]
    (B : C ⥤ D) [B.IsContinuous J J'] {T : C} (hT : IsTerminal T)
    {T' : D} (hT' : IsTerminal T') (t : T' ⟶ B.obj T)
    (M : Sheaf J' (ModuleCat.{u + 1} A))
    (f : (constantSheaf J' (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ M) :
    (constantSheafAdj J (ModuleCat.{u + 1} A) hT).homEquiv _ _
        (supportHomConstantDirectImage J J' B ≫
          (B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J J').map f) ≫
        M.obj.map t.op =
      (constantSheafAdj J' (ModuleCat.{u + 1} A) hT').homEquiv _ _ f := by
  rw [constantSheafAdj_evaluation, constantSheafAdj_evaluation]
  have he : (sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _
      (supportHomConstantDirectImage J J' B ≫
        (B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J J').map f) =
      Functor.whiskerLeft B.op
        (toSheafify J' ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A)) ≫ f.hom) := by
    rw [Adjunction.homEquiv_naturality_right]
    erw [Equiv.apply_symm_apply]
    rfl
  have ht := congr_app he (op T)
  change (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A))).app (op T) ≫
      (supportHomConstantDirectImage J J' B ≫
        (B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J J').map f).hom.app (op T) =
    (toSheafify J' ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A))).app (op (B.obj T)) ≫
      f.hom.app (op (B.obj T)) at ht
  rw [ht]
  simpa using ((toSheafify J' ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A)) ≫
    f.hom).naturality t.op).symm

private theorem etaleConstantRestrictionSpec
    {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
        Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
          (ModuleCat.of A A)).hom =
      supportHomConstantDirectImage Y.smallEtaleTopology X.smallEtaleTopology
        (MorphismProperty.Over.pullback @Etale ⊤ f) := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let a := ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).comp adj).ofNatIsoRight
    (Etale.lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) f)
  let b := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  apply ((adj.homEquiv _ _).symm).injective
  rw [Equiv.symm_apply_apply]
  apply (a.homEquiv _ _).injective
  rw [Scheme.upperStarConstantSheafIso]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  symm
  simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.apply_symm_apply]
  change (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).homEquiv _ _ (supportHomConstantDirectImage _ _ _) ≫
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A)).obj.map (PreservesTerminal.iso f.Etale).inv.op = _
  have he := constantSheafDirectImage_evaluation Y.smallEtaleTopology X.smallEtaleTopology
    f.Etale terminalIsTerminal terminalIsTerminal
    (PreservesTerminal.iso f.Etale).inv
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at he
  conv_rhs at he =>
    rw [Adjunction.homEquiv_unit]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact he

/-- The prescribed étale supported-Hom identification is represented by a
cocycle-normalized comparison record, and the comparison agrees with every
identification carried by a coordinate boundary model.

Source: Milne, Section 9, Example 9.5 and the injective-resolution proof of
Theorem 9.4; the support-kernel evaluation at one determines the comparison.
Proof: choose the normalized evaluation/cocycle record for the zero-section
support pair.  On an injective representative, the evaluation map identifies
every supported cycle with a unique map from the supported constant sheaf.
The normalization field of the given identification and the cocycle field of
the chosen record therefore agree on every cycle; injective resolutions and
naturality extend this equality to all bounded-below objects.
(blueprint: new-lem-pur-coordinate-localization-etale-identification).
-/
theorem coordinateLocalization_etale_identification_normalization
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : CoordinateBoundaryModel P T) :
    ∃ N : SupportedHomCocycleNormalization
        (etaleSupportHomPair P (zeroSection T)).topology P.Coefficient
        (etaleSupportHomPair P (zeroSection T)).isTerminal
        (etaleSupportHomPair P (zeroSection T)).restriction
        (etaleSupportHomPair P (zeroSection T)).supported
        (etaleSupportHomPair P (zeroSection T)).constantRestriction,
      ∀ (K : DerivedCategory.Plus
          (Sheaf (Line T).smallEtaleTopology
            (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ),
        M.chiEtale.chi K a = N.chi K a := by
  classical
  let S := etaleSupportHomPair P (zeroSection T)
  obtain ⟨Ne, _, _, _, _⟩ := supportedHom_cocycle_normalization P (zeroSection T)
  have hd : S.constantRestriction =
      Etale.supportedHomConstantRestriction P.Coefficient (zeroSection T) := by
    simpa [S, Etale.supportedHomConstantRestriction] using
      (etaleConstantRestrictionSpec (A := P.Coefficient) (zeroSection T)).symm
  let N₀ : SupportedHomCocycleNormalization S.topology P.Coefficient S.isTerminal
      S.restriction S.supported S.constantRestriction :=
    { theta := Ne.theta
      evaluation := by
        intro F f
        rw [hd]
        exact Ne.evaluation F f
      chi := Ne.chi
      naturality := Ne.naturality
      cocycle := Ne.cocycle }
  exact ⟨N₀, coordinateLocalization_etale_identification_extend P T M N₀
    (coordinateLocalization_etale_identification_on_injective P T M N₀)⟩

end WeilConjectures.PurityFiniteSetting
