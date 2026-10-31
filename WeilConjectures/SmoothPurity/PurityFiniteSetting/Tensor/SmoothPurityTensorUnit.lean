/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTateCoordinates
import all WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.FiniteOrientationReduction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueDerivedMonoidal

/-! # Unit evaluation of the exceptional tensor mate

Source: smooth-purity model paragraph and projection-purity-agreement normalization.
(blueprint: lem-route-smooth-purity-theta-unit).
-/

noncomputable section
set_option autoImplicit false
universe u c d e h
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

section Generic
variable {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

@[instance_reducible]
private def unitDerivedMonoidal : F.mapDerivedCategory.Monoidal :=
  letI := F.residueDerivedMonoidal
  Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory

private theorem unitDerivedMonoidal_eta :
    letI := unitDerivedMonoidal F
    Functor.OplaxMonoidal.η F.mapDerivedCategory =
      (F.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ C) ≫
        (_root_.DerivedCategory.singleFunctor D 0).map (Functor.OplaxMonoidal.η F) := by
  let := F.residueDerivedMonoidal
  change @Functor.OplaxMonoidal.η _ _ _ _ _ _ _
    (Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory).toOplaxMonoidal = _
  rw [Functor.Monoidal.transport_η]
  change F.leftDerivedFunctorIsoMapDerivedCategory.inv.app (𝟙_ _) ≫
    (F.leftDerivedFunctor.map (Functor.LaxMonoidal.ε _root_.DerivedCategory.Qh) ≫
      F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
      _root_.DerivedCategory.Qh.map
        (Functor.OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) ≫
      inv (Functor.LaxMonoidal.ε _root_.DerivedCategory.Qh)) = _
  have hC : Functor.LaxMonoidal.ε (_root_.DerivedCategory.Qh (C := C)) = 𝟙 _ := rfl
  have hD : Functor.LaxMonoidal.ε (_root_.DerivedCategory.Qh (C := D)) = 𝟙 _ := rfl
  simp only [hC, hD, IsIso.inv_id]
  erw [F.leftDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  have hf := NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac (𝟙_ _)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  rw [← hf, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [Functor.mapHomotopyCategory_η]
  change F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj (𝟙_ _)) ≫ _ = _
  rw [F.mapDerivedCategoryFactorsh_hom_app]
  change (F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app (𝟙_ _) ≫
    𝟙 _ ≫ _root_.DerivedCategory.Qh.map (𝟙 _)) ≫ _ = _
  erw [F.mapDerivedCategory.map_id, _root_.DerivedCategory.Qh.map_id]
  simp only [Category.id_comp]
  erw [Category.comp_id]
  have hq := _root_.DerivedCategory.quotientCompQhIso_hom_naturality
    (Functor.OplaxMonoidal.η (F.mapHomologicalComplex (.up ℤ)))
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at hq
  simp only [Category.comp_id, Category.id_comp] at hq
  rw [hq]
  rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Category.assoc]
  change F.mapDerivedCategoryFactors.hom.app (𝟙_ _) ≫
    _root_.DerivedCategory.Q.map (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) =
    F.mapDerivedCategoryFactors.hom.app (𝟙_ _) ≫
      _root_.DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app (𝟙_ _)) ≫
        _root_.DerivedCategory.Q.map
          ((HomologicalComplex.single D (.up ℤ) 0).map (Functor.OplaxMonoidal.η F))
  rw [← _root_.DerivedCategory.Q.map_comp]
  rfl

private theorem unitDerivedMonoidal_delta
    (K M : _root_.DerivedCategory C) :
    letI := unitDerivedMonoidal F
    Functor.OplaxMonoidal.δ F.mapDerivedCategory K M =
      ((Functor.isoWhiskerLeft ((curriedTensor (_root_.DerivedCategory C)).obj K)
          F.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
        (asIso F.leftDerivedTensorComparison).app K ≪≫
        Functor.isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory
          ((curriedTensor (_root_.DerivedCategory D)).obj (F.leftDerivedFunctor.obj K)) ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory
          ((curriedTensor (_root_.DerivedCategory D)).mapIso
            (F.leftDerivedFunctorIsoMapDerivedCategory.app K))).app M).hom := by
  let := F.residueDerivedMonoidal
  change @Functor.OplaxMonoidal.δ _ _ _ _ _ _ _
    (Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory).toOplaxMonoidal K M = _
  rw [Functor.Monoidal.transport_δ]
  change F.leftDerivedFunctorIsoMapDerivedCategory.inv.app (K ⊗ M) ≫
    (F.leftDerivedTensorComparison.app K).app M ≫
      (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app K ⊗ₘ
        F.leftDerivedFunctorIsoMapDerivedCategory.hom.app M) = _
  simp only [Iso.app_hom, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, asIso_hom, tensorHom_def']
  rfl

private theorem single_unit_inv :
    (_root_.DerivedCategory.singleFunctorObjUnitIso C).inv = 𝟙 _ := by
  have h₁ : Functor.LaxMonoidal.ε (_root_.DerivedCategory.Qh (C := C)) = 𝟙 _ := rfl
  have h₂ : Functor.LaxMonoidal.ε (HomotopyCategory.quotient C (.up ℤ)) = 𝟙 _ := rfl
  have h₃ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ :=
    fun _ ↦ rfl
  simp only [_root_.DerivedCategory.singleFunctorObjUnitIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, asIso_hom, Functor.Monoidal.εIso_hom, Iso.app_inv,
    h₁, h₂, h₃, _root_.DerivedCategory.singleFunctorIsoCompQ, Iso.refl_inv, NatTrans.id_app]
  erw [(_root_.DerivedCategory.Qh (C := C)).map_id, Category.comp_id, Category.comp_id,
    Category.id_comp]
  rfl

private theorem single_unit_hom :
    (_root_.DerivedCategory.singleFunctorObjUnitIso C).hom = 𝟙 _ := by
  have h := (_root_.DerivedCategory.singleFunctorObjUnitIso C).hom_inv_id
  rw [single_unit_inv] at h
  exact (Category.comp_id _).symm.trans h

private theorem comparison_tensor_delta (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : AlgebraicGeometry.Scheme.{u})
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    letI : IsNoetherianRing A := isNoetherian_of_finite A A
    letI := unitDerivedMonoidal (AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X)
    Functor.OplaxMonoidal.δ (AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).mapDerivedCategory K M =
      (smoothPurityComparisonTensor A X K M).hom := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  exact unitDerivedMonoidal_delta
    (AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X) K M

end Generic

section Generic
variable {C : Type c} [Category C] [Abelian C] [HasDerivedCategory C]
  {D : Type d} [Category D] [Abelian D] [HasDerivedCategory D]
  {E : Type e} [Category E] [Abelian E] [HasDerivedCategory E]
  {H : Type h} [Category H] [Abelian H] [HasDerivedCategory H]
  (F : C ⥤ D) (G : D ⥤ E) (J : C ⥤ H) (I : H ⥤ E)
  [F.Additive] [G.Additive] [J.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem square_single (s : F ⋙ G ≅ J ⋙ I) (V : C) :
    (((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso s ≪≫
      Functor.mapDerivedCategoryCompIso J I).hom.app
        ((_root_.DerivedCategory.singleFunctor C 0).obj V)) ≫
      I.mapDerivedCategory.map ((J.mapDerivedCategorySingleFunctor 0).hom.app V) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app (J.obj V) =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app V) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj V) ≫
      (_root_.DerivedCategory.singleFunctor E 0).map (s.hom.app V) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F G V]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem square_single_maps (s : F ⋙ G ≅ J ⋙ I) (V : C)
    (W : D) (W' : H) (Z : E)
    (a : F.obj V ⟶ W) (b : G.obj W ⟶ Z)
    (c : J.obj V ⟶ W') (d : I.obj W' ⟶ Z)
    (hs : s.hom.app V ≫ I.map c ≫ d = G.map a ≫ b) :
    (((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso s ≪≫
      Functor.mapDerivedCategoryCompIso J I).hom.app
        ((_root_.DerivedCategory.singleFunctor C 0).obj V)) ≫
      I.mapDerivedCategory.map ((J.mapDerivedCategorySingleFunctor 0).hom.app V ≫
        (_root_.DerivedCategory.singleFunctor H 0).map c) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app W' ≫
      (_root_.DerivedCategory.singleFunctor E 0).map d =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app V ≫
        (_root_.DerivedCategory.singleFunctor D 0).map a) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app W ≫
      (_root_.DerivedCategory.singleFunctor E 0).map b := by
  simp only [Functor.map_comp, Category.assoc]
  have hi := (I.mapDerivedCategorySingleFunctor 0).hom.naturality c
  have hg := (G.mapDerivedCategorySingleFunctor 0).hom.naturality a
  dsimp only [Functor.comp_map] at hi hg
  rw [reassoc_of% hi, reassoc_of% square_single F G J I s V, reassoc_of% hg]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc, hs, Functor.map_comp]

private theorem site_square_unit (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let V := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
    (ProEtale.sfComparisonPullbackIso A f).hom.app (𝟙_ _) ≫
      (ProEtale.comparisonUpperStar V X).map
        (Functor.OplaxMonoidal.η (Etale.upperStar V f)) ≫
      Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar V X) =
    (ProEtale.upperStar V f).map
        (Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar V Y)) ≫
      Functor.OplaxMonoidal.η (ProEtale.upperStar V f) := by
  dsimp only
  have he : ProEtale.sfComparisonDirectImageCompIso A f =
      ProEtale.lowerStarCompComparisonLowerStarIso f
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) := by
    apply Iso.ext
    ext M V
    simp [ProEtale.sfComparisonDirectImageCompIso, ProEtale.lowerStarCompComparisonLowerStarIso,
      ProEtale.sfToProEtBaseChangeIso, ProEtale.toProEtCompOverPullbackIso]
  have hm : NatTrans.IsMonoidal (ProEtale.sfComparisonDirectImageCompIso A f).inv := by
    rw [he]
    infer_instance
  exact conjugateEquiv_symm_app_unit_comp_η
    ((Etale.upperStarLowerStarAdjunction _ f).comp (ProEtale.comparisonAdjunction _ X))
    ((ProEtale.comparisonAdjunction _ Y).comp (ProEtale.upperStarLowerStarAdjunction _ f))
    (ProEtale.sfComparisonDirectImageCompIso A f).inv

private theorem tensor_unit_transport
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {M : C} (a : M ≅ 𝟙_ C) (V : C) :
    inv (Functor.OplaxMonoidal.δ F M V) ≫
        F.map (a.hom ▷ V ≫ (λ_ V).hom) =
      (F.map a.hom ≫ Functor.OplaxMonoidal.η F) ▷ F.obj V ≫
        (λ_ (F.obj V)).hom := by
  apply (cancel_epi (Functor.OplaxMonoidal.δ F M V)).1
  simp only [IsIso.hom_inv_id_assoc, comp_whiskerRight, Functor.map_comp,
    Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_left_assoc,
    Functor.OplaxMonoidal.left_unitality_hom]

private theorem tensor_unit_cancel
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {M V : C} {A W Z : D}
    (p : A ≅ F.obj M) (w : W ≅ F.obj V) (a : M ≅ 𝟙_ C)
    (e : A ⟶ 𝟙_ D) (t : F.obj V ⟶ Z) (q : W ⟶ Z)
    (hp : p.hom ≫ F.map a.hom ≫ Functor.OplaxMonoidal.η F = e)
    (hw : w.hom ≫ t = q) :
    p.hom ▷ W ≫ F.obj M ◁ w.hom ≫
      inv (Functor.OplaxMonoidal.δ F M V) ≫
      F.map (a.hom ▷ V ≫ (λ_ V).hom) ≫ t =
    e ▷ W ≫ (λ_ W).hom ≫ q := by
  rw [reassoc_of% tensor_unit_transport F a V]
  rw [reassoc_of% (whisker_exchange
      (F.map a.hom ≫ Functor.OplaxMonoidal.η F) w.hom), leftUnitor_naturality_assoc,
    ← comp_whiskerRight_assoc, hp, hw]

private theorem etale_unit_normalized (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).inv.app
        (𝟙_ _) ≫
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom =
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).hom.app
        (𝟙_ _) ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        (Functor.OplaxMonoidal.η (Etale.upperStar (ModuleCat.{u + 1} A) f)) := by
  simp only [Etale.leftDerivedUpperStarUnitIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  rw [Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem proetale_unit_normalized (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).inv.app
        (𝟙_ _) ≫
      (ProEtale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom =
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).hom.app
        (𝟙_ _) ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        (Functor.OplaxMonoidal.η (ProEtale.upperStar (ModuleCat.{u + 1} A) f)) := by
  simp only [ProEtale.leftDerivedUpperStarUnitIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  rw [Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- At the coefficient unit, the canonical exceptional tensor mate is the unit
constraint. No smoothness, affine coordinates or orientation is involved.
Source: blueprint latest, smooth-purity model paragraph;
lem-pur-projection-purity-agreement, final canonical reassociations.
(blueprint: lem-route-smooth-purity-theta-unit).

Proof: first calculate on the ordinary etale site. The tensor mate is the adjunct
of inverse projection followed by the exceptional counit. At the tensor unit,
the projection map is the unit constraint. Its inverse cancels that constraint,
and the adjunction triangle leaves the left unitor of the exceptional image.
The symmetry in smoothPurityEtaleTheta changes the right unitor to this left
unitor. The ordinary coefficient-unit isomorphism is smoothPurityUnitIso.
Transport through the monoidal site comparison and its pullback constraint.
Naturality of the comparison unit cancels its inverse occurring in
diagonalDualizingComparison against its forward occurrence in smoothPurityTheta.
The remaining pullback-unit map is exactly the explicit composite below.
Thus the two displayed morphisms agree. The calculation applies to every
compactifiable morphism, including identity morphisms and empty schemes. -/
theorem smoothPurityTheta_unit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    letI := Etale.isLeftAdjoint_rightDerivedLowerShriek P.Coefficient f
    letI : (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient)
        (HasCompactification.compactification f)).IsLeftAdjoint :=
      inferInstanceAs (Etale.rightDerivedLowerShriek
        (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
    let e :=
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory.mapIso
          (X := (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
              (Etale.ordinaryFiniteUnit P.Coefficient Y))
          (projectionUnitRaw P.Coefficient Y) ≪≫
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) f).symm.app _ ≪≫
        ProEtale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) f
    P.smoothPurityTheta f
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
            (Etale.ordinaryFiniteUnit P.Coefficient Y))
        (Etale.ordinaryFiniteUnit P.Coefficient Y) (Iso.refl _) =
      (((curriedTensor (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))).mapIso
            e).app (P.diagonalDualizing f) ≪≫
        λ_ (P.diagonalDualizing f) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
            (((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} P.Coefficient)
                (HasCompactification.compactification f))).rightAdjointUniq
              (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)).app _)).hom := by
  let := Etale.isLeftAdjoint_rightDerivedLowerShriek P.Coefficient f
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y
      (Etale.ordinaryFiniteUnit P.Coefficient Y) (P.diagonalUnitPlus Y)
  let : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
  let V := ModuleCat.{u + 1} P.Coefficient
  let F := (ProEtale.comparisonUpperStar V X).mapDerivedCategory
  let H := Etale.rightDerivedUpperShriek P.Coefficient f
  let U := Etale.ordinaryFiniteUnit P.Coefficient Y
  let K := (ProEtale.comparisonUpperStar V Y).mapDerivedCategory.obj U
  let M := (Etale.ordinaryFinitePullback P.Coefficient f).obj U
  let D := P.diagonalOrdinaryDualizing f
  let W := P.diagonalDualizing f
  let p := P.smoothPurityPullbackComparison f K U (Iso.refl _)
  let w := P.diagonalDualizingComparison f
  let a := (Etale.ordinaryFinitePullback P.Coefficient f).mapIso
      (smoothPurityUnitIso P.Coefficient Y) ≪≫
    Etale.leftDerivedUpperStarUnitIso V f
  let e := (ProEtale.upperStar V f).mapDerivedCategory.mapIso
      (projectionUnitRaw P.Coefficient Y) ≪≫
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory V f).symm.app _ ≪≫
    ProEtale.leftDerivedUpperStarUnitIso V f
  let η := (ProEtale.derivedComparisonAdjunction V Y).unit.app U
  let t := F.map (H.map η)
  let q₀ := ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification V
        (HasCompactification.compactification f))).rightAdjointUniq
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)).app
      ((ProEtale.comparisonLowerStar V Y).rightDerivedFunctor.obj K)
  let q := F.mapIso q₀
  let := unitDerivedMonoidal (ProEtale.comparisonUpperStar V X)
  have hp : p.hom ≫ F.map a.hom ≫ Functor.OplaxMonoidal.η F = e.hom := by
    have hs : (smoothPurityUnitIso P.Coefficient Y).hom = 𝟙 _ := by
      have hi := Etale.singleFunctorObjUnitIso_inv V Y
      change (smoothPurityUnitIso P.Coefficient Y).inv = 𝟙 _ at hi
      have hh := (smoothPurityUnitIso P.Coefficient Y).hom_inv_id
      rw [hi, Category.comp_id] at hh
      exact hh
    have hv : (projectionUnitRaw P.Coefficient Y).hom =
        ((ProEtale.comparisonUpperStar V Y).mapDerivedCategorySingleFunctor 0).hom.app
          (𝟙_ _) ≫ (_root_.DerivedCategory.singleFunctor _ 0).map
            (Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar V Y)) := by
      dsimp only [projectionUnitRaw, projectionSingleUnitIso, Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom]
      rw [single_unit_hom, Category.comp_id]
      rfl
    have ha : (Etale.leftDerivedUpperStarIsoMapDerivedCategory V f).inv.app U ≫ a.hom =
        ((Etale.upperStar V f).mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _) ≫
          (_root_.DerivedCategory.singleFunctor _ 0).map
            (Functor.OplaxMonoidal.η (Etale.upperStar V f)) := by
      dsimp only [a, Iso.trans_hom, Functor.mapIso_hom]
      rw [hs]
      erw [(Etale.ordinaryFinitePullback P.Coefficient f).map_id, Category.id_comp]
      exact etale_unit_normalized P.Coefficient f
    dsimp only [p, smoothPurityPullbackComparison, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Iso.symm_hom, Iso.refl_inv]
    erw [(P.smoothPurityPullback f).map_id, Category.id_comp]
    simp only [Iso.app_inv, Category.assoc]
    change (ProEtale.sfDerivedComparisonPullbackIso P.Ring f).hom.app U ≫
      F.map ((Etale.leftDerivedUpperStarIsoMapDerivedCategory V f).inv.app U) ≫
        F.map a.hom ≫ Functor.OplaxMonoidal.η F = e.hom
    rw [← F.map_comp_assoc, ha, unitDerivedMonoidal_eta]
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
    rw [proetale_unit_normalized, hv]
    exact square_single_maps (ProEtale.comparisonUpperStar V Y) (ProEtale.upperStar V f)
      (Etale.upperStar V f) (ProEtale.comparisonUpperStar V X)
      (ProEtale.sfComparisonPullbackIso P.Ring f) (𝟙_ _) (𝟙_ _) (𝟙_ _) (𝟙_ _)
      (Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar V Y))
      (Functor.OplaxMonoidal.η (ProEtale.upperStar V f))
      (Functor.OplaxMonoidal.η (Etale.upperStar V f))
      (Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar V X))
      (site_square_unit P.Ring f)
  have hw : w.hom ≫ t = q.hom := by
    change F.map (q₀.hom ≫ H.map (inv η)) ≫ F.map (H.map η) = F.map q₀.hom
    rw [← F.map_comp, Category.assoc, ← H.map_comp, IsIso.inv_hom_id,
      H.map_id, Category.comp_id]
  have ht : P.smoothPurityTheta f K U (Iso.refl _) =
      p.hom ▷ W ≫ F.obj M ◁ w.hom ≫
        (smoothPurityComparisonTensor P.Coefficient X M D).inv ≫
        F.map (a.hom ▷ D ≫ (λ_ D).hom) ≫ t := by
    simp only [smoothPurityTheta, smoothPurityTensorComparison, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
    rw [ProEtale.SpFiniteOrientation.etale_theta_unit]
    simp only [smoothPurityExceptionalComparison, Iso.app_inv, Iso.refl_inv,
      NatTrans.id_app]
    change _ ≫ _ ≫ _ ≫ _ ≫
      F.map (H.map (η ≫ (ProEtale.comparisonLowerStar V Y).rightDerivedFunctor.map
        (𝟙 K))) ≫ 𝟙 _ = _
    erw [(ProEtale.comparisonLowerStar V Y).rightDerivedFunctor.map_id,
      Category.comp_id, Category.comp_id]
    rfl
  rw [ht]
  change p.hom ▷ W ≫ F.obj M ◁ w.hom ≫
    (smoothPurityComparisonTensor P.Coefficient X M D).inv ≫
      F.map (a.hom ▷ D ≫ (λ_ D).hom) ≫ t =
    e.hom ▷ W ≫ (λ_ W).hom ≫ q.hom
  have hd := comparison_tensor_delta P.Coefficient X M D
  have hdi : (smoothPurityComparisonTensor P.Coefficient X M D).inv =
      inv (Functor.OplaxMonoidal.δ F M D) := by
    apply IsIso.eq_inv_of_hom_inv_id
    rw [hd]
    exact (smoothPurityComparisonTensor P.Coefficient X M D).hom_inv_id
  rw [hdi]
  exact tensor_unit_cancel F p w a e.hom t q.hom hp hw

end Generic

@[expose] public section

set_option maxHeartbeats 1000000 in
-- Normalize the large exact-derived pullback and tensor comparison composites.
end

end WeilConjectures.PurityFiniteSetting
