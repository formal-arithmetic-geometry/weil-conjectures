/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Identity coefficient multiplication and its finite quotient tensor square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
attribute [local instance 5000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

-- Exact derived localization preserves the two restriction-unit constraints.

private theorem derived_left_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (V : B ⥤ A) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (U : A ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (ρ : U ≅ 𝟭 A) :
    (Functor.mapDerivedCategoryCompIso V U).symm ≪≫
        Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft V ρ) =
      Functor.isoWhiskerLeft V.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso A) ≪≫
        Functor.rightUnitor V.mapDerivedCategory := by
  apply Iso.ext
  ext X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft V ρ) X
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id V) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hn hu
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso V U).hom.app X)).mp
  rw [Iso.hom_inv_id_app_assoc]
  simp only [← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  simp only [NatTrans.id_app] at hu
  rw [reassoc_of% hu]
  erw [Category.comp_id, Category.comp_id]

private theorem derived_right_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (U : B ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (V : B ⥤ A) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (ρ : U ≅ 𝟭 B) :
    (Functor.mapDerivedCategoryCompIso U V).symm ≪≫
        Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight ρ V) =
      Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso B)
          V.mapDerivedCategory ≪≫ Functor.leftUnitor V.mapDerivedCategory := by
  apply Iso.ext
  ext X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight ρ V) X
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp V) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hn hu
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U V).hom.app X)).mp
  rw [Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  simp only [NatTrans.id_app] at hu
  rw [reassoc_of% hu]
  erw [Category.comp_id, Category.comp_id]

private theorem comparison_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {U : B ⥤ A} {V : C ⥤ B} {W : C ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (d : V ⋙ U ≅ W) (M : A) :
    (a.comp b).homEquiv M _ ((a.leftAdjointCompIso b c d).hom.app M) ≫
      d.hom.app (H.obj M) = c.unit.app M := by
  rw [Adjunction.homEquiv_unit, Category.assoc, d.hom.naturality, ← Category.assoc]
  have hu := unit_conjugateEquiv (a.comp b) c (a.leftAdjointCompIso b c d).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
  rw [hu, Category.assoc, ← W.map_comp, Iso.inv_hom_id_app, W.map_id]
  exact Category.comp_id _

private theorem normalizedComparison_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {U : B ⥤ A} {V : C ⥤ B} {W : C ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (d : V ⋙ U ≅ W) :
    ((a.comp b).ofNatIsoRight d).leftAdjointUniq c =
      a.leftAdjointCompIso b c d := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (((a.comp b).ofNatIsoRight d).homEquiv M _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply]
  exact (comparison_unit a b c d M).symm

-- Transfer the restriction-unit constraints through uniqueness of left adjoints.

private theorem tensorComposition_unit_left {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (r : R ⟶ S) :
    PurCompactSupport.tensorComposition (𝟙 R) r r (Category.id_comp _) =
      Functor.isoWhiskerRight (PurCompactSupport.tensorIdentity R) (pbcDerivedExtend r) ≪≫
        Functor.leftUnitor (pbcDerivedExtend r) := by
  let ρ := (PurCompactSupport.restrictIdentity_existsUnique.{u} R).exists.choose
  let δ := Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso _
  have he : pbcRestrictComp (𝟙 R) r r (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcRestrict r) ρ := by
    apply Iso.ext
    ext M U x
    exact (pbcRestrictComp_exists (𝟙 R) r r
      (Category.id_comp _)).exists.choose_spec M U x |>.trans
        ((PurCompactSupport.restrictIdentity_existsUnique R).exists.choose_spec
          ((pbcRestrict r).obj M) U x).symm
  have hd : pbcDerivedRestrictComp (𝟙 R) r r (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcDerivedRestrict r) δ ≪≫
        Functor.rightUnitor (pbcDerivedRestrict r) := by
    unfold pbcDerivedRestrictComp
    rw [he]
    exact derived_left_unit (pbcRestrict r) (pbcRestrict (𝟙 R)) ρ
  unfold PurCompactSupport.tensorComposition
  rw [normalizedComparison_eq]
  exact Adjunction.leftAdjointCompIso_id_comp (pbcDerivedScalarAdjunction (𝟙 R))
    (pbcDerivedScalarAdjunction r) _ δ hd

private theorem tensorComposition_unit_right {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (r : R ⟶ S) :
    PurCompactSupport.tensorComposition r (𝟙 S) r (Category.comp_id _) =
      Functor.isoWhiskerLeft (pbcDerivedExtend r) (PurCompactSupport.tensorIdentity S) ≪≫
        Functor.rightUnitor (pbcDerivedExtend r) := by
  let ρ := (PurCompactSupport.restrictIdentity_existsUnique.{u} S).exists.choose
  let δ := Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso _
  have he : pbcRestrictComp r (𝟙 S) r (Category.comp_id _) =
      Functor.isoWhiskerRight ρ (pbcRestrict r) := by
    apply Iso.ext
    ext M U x
    exact (pbcRestrictComp_exists r (𝟙 S) r
      (Category.comp_id _)).exists.choose_spec M U x |>.trans
        ((PurCompactSupport.restrictIdentity_existsUnique S).exists.choose_spec M U x).symm
  have hd : pbcDerivedRestrictComp r (𝟙 S) r (Category.comp_id _) =
      Functor.isoWhiskerRight δ (pbcDerivedRestrict r) ≪≫
        Functor.leftUnitor (pbcDerivedRestrict r) := by
    unfold pbcDerivedRestrictComp
    rw [he]
    exact derived_right_unit (pbcRestrict (𝟙 S)) (pbcRestrict r) ρ
  unfold PurCompactSupport.tensorComposition
  rw [normalizedComparison_eq]
  exact Adjunction.leftAdjointCompIso_comp_id (pbcDerivedScalarAdjunction r)
    (pbcDerivedScalarAdjunction (𝟙 S)) _ δ hd

private theorem cancel_units
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ C) (G : D ⥤ D) (r : C ⥤ D) (e : F ≅ 𝟭 C) (f : G ≅ 𝟭 D) (K : C) :
    ((Functor.isoWhiskerRight e r ≪≫ Functor.leftUnitor r) ≪≫
      (Functor.isoWhiskerLeft r f ≪≫ Functor.rightUnitor r).symm).hom.app K ≫
        f.hom.app (r.obj K) = r.map (e.hom.app K) := by
  simp

private theorem tensorSquare_unit_aux {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (r d : R ⟶ S)
    (hd : d = r) (h₁ : 𝟙 R ≫ r = d) (h₂ : r ≫ 𝟙 S = d)
    (K : DerivedCategory (pbcModules W R)) :
    (PurCompactSupport.tensorComposition (𝟙 R) r d h₁ ≪≫
      (PurCompactSupport.tensorComposition r (𝟙 S) d h₂).symm).hom.app K ≫
        (PurCompactSupport.tensorIdentity S).hom.app ((pbcDerivedExtend r).obj K) =
      (pbcDerivedExtend r).map ((PurCompactSupport.tensorIdentity R).hom.app K) := by
  subst d
  rw [tensorComposition_unit_left, tensorComposition_unit_right]
  exact cancel_units (pbcDerivedExtend (𝟙 R)) (pbcDerivedExtend (𝟙 S))
    (pbcDerivedExtend r) (PurCompactSupport.tensorIdentity R)
    (PurCompactSupport.tensorIdentity S) K

private theorem tensorSquare_unit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (r : R ⟶ S)
    (h : (𝟙 R) ≫ r = r ≫ 𝟙 S) (K : DerivedCategory (pbcModules W R)) :
    (PurCompactSupport.tensorSquare (𝟙 R) (𝟙 S) r r h).hom.app K ≫
        (PurCompactSupport.tensorIdentity S).hom.app ((pbcDerivedExtend r).obj K) =
      (pbcDerivedExtend r).map ((PurCompactSupport.tensorIdentity R).hom.app K) := by
  exact tensorSquare_unit_aux r _ (Category.id_comp r) rfl h.symm K
attribute [local irreducible] PurCompactSupport.tensorSquare

private theorem square_heq
    {C D I J : Type*} [Category C] [Category D]
    (F : I → C ⥤ C) (G : J → D ⥤ D) (r : C ⥤ D)
    (P : I → J → Prop) (s : ∀ i j, P i j → (F i ⋙ r ≅ r ⋙ G j))
    (i₀ : I) (j₀ : J) (i : I) (j : J) (hi : i = i₀) (hj : j = j₀)
    (h : P i j) (h₀ : P i₀ j₀) : HEq (s i j h) (s i₀ j₀ h₀) := by
  subst i
  subst j
  rfl

private theorem square_unit_of_heq
    {C D : Type*} [Category C] [Category D] (r : C ⥤ D)
    {F F₀ : C ⥤ C} {G G₀ : D ⥤ D}
    (b : F ⋙ r ≅ r ⋙ G) (b₀ : F₀ ⋙ r ≅ r ⋙ G₀)
    (hF : F = F₀) (hG : G = G₀) (hb : HEq b b₀)
    (e : F₀ ≅ 𝟭 C) (f : G₀ ≅ 𝟭 D) (K : C)
    (hu : b₀.hom.app K ≫ f.hom.app (r.obj K) = r.map (e.hom.app K)) :
    b.hom.app K ≫ (eqToIso hG ≪≫ f).hom.app (r.obj K) =
      r.map ((eqToIso hF ≪≫ e).hom.app K) := by
  subst F
  subst G
  cases eq_of_heq hb
  simpa only [eqToIso_refl, Iso.refl_trans] using hu

private theorem tensorSquare_unit_of_eq {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ R) (b : S ⟶ S) (r : R ⟶ S)
    (ha : a = 𝟙 R) (hb : b = 𝟙 S) (h : a ≫ r = r ≫ b)
    (K : DerivedCategory (pbcModules W R)) :
    (PurCompactSupport.tensorSquare (W := W) a b r r h).hom.app K ≫
        (eqToIso (congrArg (fun f : S ⟶ S ↦ pbcDerivedExtend (X := W) f) hb) ≪≫
          PurCompactSupport.tensorIdentity S).hom.app ((pbcDerivedExtend r).obj K) =
      (pbcDerivedExtend r).map
        ((eqToIso (congrArg (fun f : R ⟶ R ↦ pbcDerivedExtend (X := W) f) ha) ≪≫
          PurCompactSupport.tensorIdentity R).hom.app K) := by
  let F := fun f : R ⟶ R ↦ pbcDerivedExtend (X := W) f
  let G := fun f : S ⟶ S ↦ pbcDerivedExtend (X := W) f
  have h₀ : 𝟙 R ≫ r = r ≫ 𝟙 S := by simp only [Category.id_comp, Category.comp_id]
  have hs := square_heq F G (pbcDerivedExtend (X := W) r)
    (fun a b ↦ a ≫ r = r ≫ b)
    (fun a b h ↦ PurCompactSupport.tensorSquare (W := W) a b r r h)
    (𝟙 R) (𝟙 S) a b ha hb h h₀
  have hh := square_unit_of_heq (pbcDerivedExtend (X := W) r)
    (PurCompactSupport.tensorSquare (W := W) a b r r h)
    (PurCompactSupport.tensorSquare (W := W) (𝟙 R) (𝟙 S) r r h₀)
    (congrArg F ha) (congrArg G hb) hs
    (PurCompactSupport.tensorIdentity R) (PurCompactSupport.tensorIdentity S) K
    (tensorSquare_unit (W := W) r h₀ K)
  exact hh

-- Give the comparison its unrestricted-projection type once, so later calculations
-- do not repeatedly unfold the positive-index coefficient presentation.

private def reductionIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) :
    pbcDerivedExtend (completedIntegralCommRingProjectionUnrestricted l E X n) ≅
      scalarReductionDerivedExtension l E X n :=
  PurCompactSupport.finiteReductionIso l E X n

attribute [local irreducible] reductionIso

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] completion PurCompactSupport.finiteReductionIso
  PurCompactSupport.tensorIdentity scalarReductionDerivedExtension
attribute [local semireducible] reductionIso

private theorem quotient_iso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ)
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    quotient l E E (AlgHom.id (Padic l) E) X n K hK =
      (scalarReductionDerivedExtension l E X n).mapIso
          (completion l E E (AlgHom.id (Padic l) E) X K hK).symm ≪≫
        (reductionIso l E X n).symm.app
          ((pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)).obj K) ≪≫
        (PurCompactSupport.tensorSquare
          (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)
          (integralScalarQuotientSheafMap l E E (AlgHom.id (Padic l) E) X n)
          (completedIntegralCommRingProjectionUnrestricted l E X n)
          (completedIntegralCommRingProjectionUnrestricted l E X n)
          ((completedCoefficientMap_existsUnique l E E
            (AlgHom.id (Padic l) E) X).exists.choose_spec n)).app K ≪≫
        (pbcDerivedExtend
          (integralScalarQuotientSheafMap l E E (AlgHom.id (Padic l) E) X n)).mapIso
          ((reductionIso l E X n).app K) := by
  rfl

attribute [local irreducible] reductionIso

private theorem expand_unit_iso
    {C : Type*} [Category C] {F H : C ⥤ C}
    (e : F ≅ H) (f : H ≅ 𝟭 C) (K T : C) (c : F.obj K ≅ T) :
    c.symm ≪≫ e.app K ≪≫ f.app K = c.symm ≪≫ (e ≪≫ f).app K := by
  apply Iso.ext
  rfl

private theorem unit_iso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    unit l E X K hK =
      (completion l E E (AlgHom.id (Padic l) E) X K hK).symm ≪≫
        (eqToIso (congrArg
          (fun φ ↦ pbcDerivedExtend φ)
          (PurCompactSupport.completedMap_identity l E X)) ≪≫
            PurCompactSupport.tensorIdentity
              (completedIntegralCommRingSheafUnrestricted l E X)).app K := by
  exact expand_unit_iso
    (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X)))
    (PurCompactSupport.tensorIdentity (completedIntegralCommRingSheafUnrestricted l E X))
    K _ (completion l E E (AlgHom.id (Padic l) E) X K hK)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem conjugated_square_unit
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ C) (G : D ⥤ D) (H J : C ⥤ D) (ρ : H ≅ J)
    (b : F ⋙ H ≅ H ⋙ G) (e : F ≅ 𝟭 C) (f : G ≅ 𝟭 D)
    (K T : C) (c : F.obj K ≅ T)
    (h : b.hom.app K ≫ f.hom.app (H.obj K) = H.map (e.hom.app K)) :
    J.map (c.inv ≫ e.hom.app K) =
      (J.map c.inv ≫ ρ.inv.app (F.obj K) ≫ b.hom.app K ≫
        G.map (ρ.hom.app K)) ≫ f.hom.app (J.obj K) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [f.hom.naturality]
  simp only [Functor.id_map]
  rw [← Category.assoc (b.hom.app K), h]
  simpa only [Functor.id_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using
    congrArg (fun t ↦ J.map c.inv ≫ t ≫ ρ.hom.app K)
      (ρ.inv.naturality (e.hom.app K))

private theorem conjugated_square_unit_iso
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ C) (G : D ⥤ D) (H J : C ⥤ D) (ρ : H ≅ J)
    (b : F ⋙ H ≅ H ⋙ G) (e : F ≅ 𝟭 C) (f : G ≅ 𝟭 D)
    (K T : C) (c : F.obj K ≅ T)
    (h : b.hom.app K ≫ f.hom.app (H.obj K) = H.map (e.hom.app K)) :
    J.mapIso (c.symm ≪≫ e.app K) =
      (J.mapIso c.symm ≪≫ ρ.symm.app (F.obj K) ≪≫ b.app K ≪≫
        G.mapIso (ρ.app K)) ≪≫ f.app (J.obj K) := by
  apply Iso.ext
  simpa only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
    using conjugated_square_unit F G H J ρ b e f K T c h

private theorem ring_quotient_unit_iso
    {W : Scheme.{u}} {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ R) (b : S ⟶ S) (r : R ⟶ S)
    (ha : a = 𝟙 R) (hb : b = 𝟙 S) (h : a ≫ r = r ≫ b)
    (J : _) (ρ : pbcDerivedExtend r ≅ J)
    (K T : _) (c : (pbcDerivedExtend a).obj K ≅ T) :
    J.mapIso (c.symm ≪≫
      (eqToIso (congrArg (fun f : R ⟶ R ↦ pbcDerivedExtend (X := W) f) ha) ≪≫
        PurCompactSupport.tensorIdentity R).app K) =
      (J.mapIso c.symm ≪≫ ρ.symm.app ((pbcDerivedExtend a).obj K) ≪≫
        (PurCompactSupport.tensorSquare a b r r h).app K ≪≫
          (pbcDerivedExtend b).mapIso (ρ.app K)) ≪≫
      (eqToIso (congrArg (fun f : S ⟶ S ↦ pbcDerivedExtend (X := W) f) hb) ≪≫
        PurCompactSupport.tensorIdentity S).app (J.obj K) := by
  exact conjugated_square_unit_iso
    (pbcDerivedExtend (X := W) a) (pbcDerivedExtend (X := W) b)
    (pbcDerivedExtend (X := W) r) J ρ
    (PurCompactSupport.tensorSquare a b r r h)
    (eqToIso (congrArg (fun f : R ⟶ R ↦ pbcDerivedExtend (X := W) f) ha) ≪≫
      PurCompactSupport.tensorIdentity R)
    (eqToIso (congrArg (fun f : S ⟶ S ↦ pbcDerivedExtend (X := W) f) hb) ≪≫
      PurCompactSupport.tensorIdentity S)
    K T c (tensorSquare_unit_of_eq a b r ha hb h K)

-- Conjugate the tensor-square unit equation by the specified completion comparison.

attribute [local irreducible] unit quotient
  completedIntegralCommRingSheafUnrestricted
  completedIntegralCommRingProjectionUnrestricted integralScalarQuotientSheafMap
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Compare the coefficient presentations before unfolding derived localization.
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  SheafOfModules.instAbelian

private theorem hom_of_mapIso_eq
    {C D : Type*} [Category C] [Category D]
    (J : C ⥤ D) {K T : C} {L : D}
    (u : T ≅ K) (q : J.obj T ≅ L) (f : L ≅ J.obj K)
    (h : J.mapIso u = q ≪≫ f) :
    J.map u.hom = q.hom ≫ f.hom := by
  simpa only [Functor.mapIso_hom, Iso.trans_hom] using congrArg Iso.hom h

private theorem quotient_multiplication_unit_iso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ)
    (hq : integralScalarQuotientSheafMap l E E (AlgHom.id (Padic l) E) X n = 𝟙 _)
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (scalarReductionDerivedExtension l E X n).mapIso (unit l E X K hK) =
      quotient l E E (AlgHom.id (Padic l) E) X n K hK ≪≫
        (eqToIso (congrArg (fun f : integralCoefficientCommRingSheaf l E X n ⟶
        integralCoefficientCommRingSheaf l E X n ↦ pbcDerivedExtend (X := X) f) hq) ≪≫
          PurCompactSupport.tensorIdentity (integralCoefficientCommRingSheaf l E X n)).app
          ((scalarReductionDerivedExtension l E X n).obj K) := by
  rw [unit_iso, quotient_iso]
  exact ring_quotient_unit_iso
      (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)
      (integralScalarQuotientSheafMap l E E (AlgHom.id (Padic l) E) X n)
      (completedIntegralCommRingProjectionUnrestricted l E X n)
      (PurCompactSupport.completedMap_identity l E X) hq
      ((completedCoefficientMap_existsUnique l E E
        (AlgHom.id (Padic l) E) X).exists.choose_spec n)
      (scalarReductionDerivedExtension l E X n) (reductionIso l E X n)
      K _ (completion l E E (AlgHom.id (Padic l) E) X K hK)

/-- Reduction of the completed multiplication unit equals the specified quotient
comparison followed by multiplication at the finite coefficient level.
Source: current blueprint `lem-coef-integral-finite-extension`, final paragraph,
unit equations transported from the finite comparisons.
(blueprint: lem-sf-integral-finite-extension-quotient-multiplication-unit)

Proof: expand `unit` as inverse completion followed by the completed tensor unit.
Expand `quotient` as reduction of inverse completion, inverse `finiteReductionIso`,
the coefficient tensor square, and extension of `finiteReductionIso`. Cancel the
common reduction of inverse completion. The two tensor-composition unit laws,
obtained by adjoint uniqueness from the ordinary restriction unit constraints and
exact derived localization, imply `tensorSquare_unit_of_eq`. Its hypotheses hold
because `completedMap_identity` identifies the completed coefficient map with the
identity and `hq` identifies the finite coefficient map with the identity.
Use naturality of the finite tensor unit to move it past the finite-reduction
comparison, then apply that tensor-square unit equation. Naturality of
`finiteReductionIso` identifies the remaining composite with reduction of the
completed tensor unit. This calculation requires no dualizing object, geometry
of X, or nonzero level, so it holds also for zero objects and n=0. The private
helpers above prove the two tensor-composition unit laws, their tensor-square
consequence, and the expansions of `unit` and `quotient`. Associativity and
naturality combine these identities to give the asserted equality. -/
theorem quotient_multiplication_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ)
    (hq : integralScalarQuotientSheafMap l E E (AlgHom.id (Padic l) E) X n = 𝟙 _)
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (scalarReductionDerivedExtension l E X n).map (unit l E X K hK).hom =
      (quotient l E E (AlgHom.id (Padic l) E) X n K hK).hom ≫
        (eqToIso (congrArg (fun f : integralCoefficientCommRingSheaf l E X n ⟶
        integralCoefficientCommRingSheaf l E X n ↦ pbcDerivedExtend (X := X) f) hq) ≪≫
          PurCompactSupport.tensorIdentity (integralCoefficientCommRingSheaf l E X n)).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K) := by
  exact hom_of_mapIso_eq (scalarReductionDerivedExtension l E X n) _ _ _
    (quotient_multiplication_unit_iso l E X n hq K hK)

end WeilConjectures.IntegralFiniteExtension
