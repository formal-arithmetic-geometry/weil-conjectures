/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenProjectionMate
public import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateData
import all WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenAlphaSiteTransport
import all WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientOrdinaryClopenLocalization
import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
import all WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization

/-! # Exact alpha comparison across the bounded-below inclusion -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

set_option Elab.async false

universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Limits

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorPlus
  upperStar lowerStar openImmersionLowerShriek Functor.leftAdjoint
  leftDerivedUpperStarIsoMapDerivedCategory properOpenAlpha

private theorem cancel_exact_comparison
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (e : X ≅ Y) {Z : D} (f : Z ⟶ F.obj Y) (g : Z ⟶ F.obj X)
    (h : f ≫ F.map e.inv = g) : f = g ≫ F.map e.hom := by
  apply (cancel_mono (F.map e.inv)).1
  simpa only [Category.assoc, ← F.map_comp, Iso.hom_inv_id,
    F.map_id, Category.comp_id] using h

section ExactSquares

open AlgebraicGeometry.Etale.ClopenMateNormalization

variable {A B C D : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory D]
  (G : A ⥤ B) (Q : B ⥤ D) (P : A ⥤ C) (H : C ⥤ D)
  [G.Additive] [Q.Additive] [P.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private theorem inclusion_map_exact {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map f) =
      G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

private theorem inclusion_map_Qh {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map f) =
      DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι A).map f) := rfl

private theorem localizedSquarePlus_inclusion (e : G ⋙ Q ⟶ P ⋙ H)
    (K : DerivedCategory.Plus A) :
    DerivedCategory.Plus.ι.map ((clopenLocalizedSquarePlus e).app K) =
      (clopenLocalizedSquare e).app K.obj := by
  suffices he : Functor.whiskerRight (clopenLocalizedSquarePlus e) DerivedCategory.Plus.ι =
      Functor.whiskerLeft DerivedCategory.Plus.ι (clopenLocalizedSquare e) from
    congr_app he K
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso A)
  intro L
  apply (cancel_mono (H.mapDerivedCategory.map
    (P.mapDerivedCategoryFactorsh.hom.app L.obj) ≫
      H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj L.obj))).1
  have hp := congrArg (fun f ↦ DerivedCategory.Plus.ι.map f)
    (clopenLocalizedSquarePlus_factorization e L)
  simp only [Functor.map_comp, inclusion_map_exact,
    Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app, inclusion_map_Qh,
    NatTrans.ι_map_mapHomotopyCategoryPlus_app] at hp
  exact hp.trans (clopenLocalizedSquare_fach e L.obj).symm

end ExactSquares

private theorem plus_alpha_inclusion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.ι.map ((cbcClopenAlphaPlus Λ k i r p h).app K) =
      (Etale.ClopenMateNormalization.clopenLocalizedSquare
        (cbcClopenAlphaSheaf Λ k i r p h)).app K.obj := by
  have he := congr_app (ExactAlphaLocalization.baseChange_eq
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (upperStar (ModuleCat.{u + 1} Λ) p)
    (upperStar (ModuleCat.{u + 1} Λ) r)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (cbcClopenAlphaSheaf Λ k i r p h)) K
  change (cbcClopenAlphaPlus Λ k i r p h).app K =
    (Etale.ClopenMateNormalization.clopenLocalizedSquarePlus
      (cbcClopenAlphaSheaf Λ k i r p h)).app K at he
  rw [he]
  exact localizedSquarePlus_inclusion _ _ _ _ _ K

private theorem cbc_open_comp_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    (proEtaleOpenExtensionComp Λ j b).inv = (AmbientClopen.openComp Λ j b).hom := by
  change ((((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b)).ofNatIsoRight
      (upperStarComp (ModuleCat.{u + 1} Λ) j b).symm).leftAdjointUniq
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) (j ≫ b))).hom = _
  exact congrArg Iso.hom (WeilConjectures.AmbientCompositor.left_comp_unique _ _ _ _)

private theorem cbc_open_congr_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) : cbcOpenCongr Λ h = AmbientClopen.openCongr Λ h := by
  subst k
  exact (AmbientClopen.ordinary_open_congr_refl Λ j).symm

private theorem cbc_pull_congr_eq
    (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} (h : j = k) :
    cbcPullCongr Λ h = upperStarCongr (ModuleCat.{u + 1} Λ) h := by
  subst k
  rfl

private theorem cbc_beta_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion b]
    (sq : IsPullback a b j g) :
    letI := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq
    inv (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) =
      (AmbientClopen.beta Λ a b j g sq).hom := by
  have he : (AmbientClopen.beta Λ a b j g sq).symm =
      openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq := by
    apply Iso.ext
    rfl
  change (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq).inv = _
  rw [← he]
  rfl

private theorem cbc_expanded_word_eq
    {A B C D E : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E]
    (I : A ⥤ E) (P : E ⥤ D) (Q : A ⥤ B) (S : B ⥤ C)
    (J : C ⥤ B) (B₀ : B ⥤ D) (K : C ⥤ D) (R : A ⥤ C)
    (β : I ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q ⋙ S ⟶ R) :
    β ≫ Functor.whiskerRight (Functor.whiskerLeft Q π) B₀ ≫
      Functor.whiskerRight (Functor.associator Q S J).inv B₀ ≫
      (Functor.associator (Q ⋙ S) J B₀).hom ≫ Functor.whiskerLeft (Q ⋙ S) c ≫
      Functor.whiskerRight d K = clopenMateComposite I P Q S J B₀ K R β π c d := by
  apply NatTrans.ext
  funext M
  simp only [clopenMateComposite_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.comp_obj, Category.id_comp]
  erw [B₀.map_id]
  simp only [Category.id_comp]

private theorem alpha_sheaf_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    cbcClopenAlphaSheaf Λ k i r p h = AmbientClopen.alpha Λ k r p i h := by
  let := (StrictTower.squareLift_clopen k r p i h).1
  let := (StrictTower.squareLift_clopen k r p i h).2
  have hb := cbc_beta_eq Λ (pullback.snd p i) (pullback.fst p i) i p
    (IsPullback.of_hasPullback p i).flip
  unfold cbcClopenAlphaSheaf
  dsimp only
  rw [hb, cbc_expanded_word_eq]
  unfold AmbientClopen.alpha AmbientClopen.sheafAlpha
  rw [cbc_open_comp_eq, cbc_open_congr_eq, cbc_pull_congr_eq]
  rfl

/-- Exact localization identifies the two clopen alpha words before taking mates.
Source: Step 1 of lem-pur-refinement-mate-plus-compatibility; Stacks Tags 015F,
09AF and 0F7B (blueprint: lem-pur-refinement-alpha-plus-inclusion).

Proof: normalize the exact right-derived base-change word as the localization of
cbcClopenAlphaSheaf, using its factorization at bounded-below homotopy objects.
Localization uniqueness and the compatibility of the exact functor factorizations
with inclusion identify its image in D with clopenLocalizedSquare of the sheaf word.
Compare that sheaf word with AmbientClopen.alpha: the cartesian beta has the same
conjugate, the clopen projector is identical, the open compositor agrees by uniqueness
of left adjoints, and equality transport agrees by equality induction. Apply
ordinary_alpha_localized, which identifies the localization of this full word with
properOpenAlpha through the total-to-exact inverse-image comparisons. Evaluate at K
and cancel the inverse comparison for the identity pullback. This proves the stated
formula, including empty schemes and the zero coefficient ring. -/
theorem properOpenRefinementAlpha_plus_inclusion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X T₁ T₂ : Scheme.{u}} (r : T₁ ⟶ T₂) [IsProper r]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (h : j₁ ≫ r = j₂)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) r).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategory.obj K.obj) ≫
      DerivedCategory.Plus.ι.map
        ((cbcClopenAlphaPlus Λ j₁ j₂ (𝟙 X) r
          (h.trans (Category.id_comp j₂).symm)).app K) =
    (properOpenAlpha Λ j₁ (𝟙 X) r j₂
        (h.trans (Category.id_comp j₂).symm)).app K.obj ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategory.map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (𝟙 X)).hom.app
          K.obj) := by
  let hh := h.trans (Category.id_comp j₂).symm
  rw [plus_alpha_inclusion, alpha_sheaf_eq]
  have hs : Etale.ClopenMateNormalization.clopenLocalizedSquare
      (AmbientClopen.alpha Λ j₁ (𝟙 X) r j₂ hh) =
      AmbientClopen.localizeSquare _ _ _ _ (AmbientClopen.alpha Λ j₁ (𝟙 X) r j₂ hh) := by
    unfold Etale.ClopenMateNormalization.clopenLocalizedSquare
      AmbientClopen.localizeSquare AmbientClopen.localize
    rfl
  rw [hs]
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategory
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (𝟙 X)
  have he := congr_app (AmbientClopen.ordinary_alpha_localized Λ j₁ (𝟙 X) r j₂ hh) K.obj
  change (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) r).hom.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategory.obj K.obj) ≫
    (AmbientClopen.localizeSquare _ _ _ _
      (AmbientClopen.alpha Λ j₁ (𝟙 X) r j₂ hh)).app K.obj ≫
      J.map (e.inv.app K.obj) = (properOpenAlpha Λ j₁ (𝟙 X) r j₂ hh).app K.obj at he
  let f := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) r).hom.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategory.obj K.obj) ≫
    (AmbientClopen.localizeSquare _ _ _ _
      (AmbientClopen.alpha Λ j₁ (𝟙 X) r j₂ hh)).app K.obj
  let g := (properOpenAlpha Λ j₁ (𝟙 X) r j₂ hh).app K.obj
  have hc : f ≫ J.map (e.app K.obj).inv = g := by
    simpa only [f, g, Category.assoc, Iso.app_inv] using he
  simpa only [Iso.app_hom] using cancel_exact_comparison J (e.app K.obj) f g hc

end AlgebraicGeometry.ProEtale
