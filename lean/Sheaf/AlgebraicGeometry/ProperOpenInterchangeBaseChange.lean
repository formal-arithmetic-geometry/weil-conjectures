/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-! # Coherence of the normalized proper/open comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem mono_ordinaryOpenInclusion (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app F) := by
  obtain ⟨L, ι, hι, hp, ho, hrest⟩ := properSupportSheafComposition Λ
  obtain ⟨o, ho⟩ := ho X Y j
  have hmono : Mono ((ι j).app F) := by
    have happ (V : Y.Etaleᵒᵖ) : Mono (((ι j).app F).hom.app V) :=
      (ModuleCat.mono_iff_injective _).2 (hι X Y j F V.unop).1
    have : Mono ((ι j).app F).hom := NatTrans.mono_of_mono_app _
    exact Sheaf.Hom.mono_of_presheaf_mono Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) ((ι j).app F)
  have heq := congr_app ho F
  dsimp only [NatTrans.comp_app] at heq
  rw [← heq]
  infer_instance

private theorem ordinaryBaseChange_comp (Λ : Type (u + 1)) [CommRing Λ]
    {W X Y W₁ X₁ Y₁ : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (f₁ : W₁ ⟶ X₁) (g₁ : X₁ ⟶ Y₁)
    (a : W₁ ⟶ W) (b : X₁ ⟶ X) (d : Y₁ ⟶ Y)
    (sqf : CommSq a f₁ f b) (sqg : CommSq b g₁ g d)
    (fg : W ⟶ Y) (f₁g₁ : W₁ ⟶ Y₁) (h : fg = f ≫ g) (h₁ : f₁g₁ = f₁ ≫ g₁)
    (sq : CommSq a f₁g₁ fg d)
    (F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) d).map
        ((lowerStarComp (ModuleCat.{u + 1} Λ) f g fg h).hom.app F) ≫
      (baseChangeMap (ModuleCat.{u + 1} Λ) sq).app F =
    (baseChangeMap (ModuleCat.{u + 1} Λ) sqg).app
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) g₁).map
        ((baseChangeMap (ModuleCat.{u + 1} Λ) sqf).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) f₁ g₁ f₁g₁ h₁).hom.app
        ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) := by
  subst fg
  subst f₁g₁
  rw [baseChangeMap_paste_vert_app _ sqf sqg sq F]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

private theorem ordinaryOpenBaseChange_inclusion (Λ : Type (u + 1)) [CommRing Λ]
    {U U₁ X X₁ : Scheme.{u}} (j : U ⟶ X) (j₁ : U₁ ⟶ X₁)
    [IsOpenImmersion j] [IsOpenImmersion j₁]
    (a : U₁ ⟶ U) (b : X₁ ⟶ X) (sq : IsPullback a j₁ j b)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} Λ) sq)).inv.app F ≫
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j₁).app
        ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) =
    (upperStar (ModuleCat.{u + 1} Λ) b).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app F) ≫
      (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F := by
  have := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq
  rw [← openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app
    (ModuleCat.{u + 1} Λ) sq.toCommSq F, ← Category.assoc, ← Category.assoc]
  simp only [asIso_inv, ← NatTrans.comp_app, IsIso.inv_hom_id,
    NatTrans.id_app, Category.id_comp]

private theorem ordinaryInterchange_cube (Λ : Type (u + 1)) [CommRing Λ]
    {A B C D A₁ B₁ C₁ D₁ : Scheme.{u}}
    (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (a : B₁ ⟶ B) (b : D₁ ⟶ D) (c : C₁ ⟶ C) (d : A₁ ⟶ A)
    (k₁ : A₁ ⟶ B₁) (i₁ : C₁ ⟶ D₁) (r₁ : A₁ ⟶ C₁) (p₁ : B₁ ⟶ D₁)
    [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
    (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (sr : IsPullback d r₁ r c) (sp : IsPullback a p₁ p b)
    (δ : lowerStar (ModuleCat.{u + 1} Λ) r ⋙ openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙ lowerStar (ModuleCat.{u + 1} Λ) p)
    (δ₁ : lowerStar (ModuleCat.{u + 1} Λ) r₁ ⋙ openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁ ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k₁ ⋙ lowerStar (ModuleCat.{u + 1} Λ) p₁)
    (hδ : ∀ F, δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app
        ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F)
    (hδ₁ : ∀ F, δ₁.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p₁).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k₁).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) k₁ p₁).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i₁).app
        ((lowerStar (ModuleCat.{u + 1} Λ) r₁).obj F) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) r₁ i₁ (k₁ ≫ p₁) h₁).hom.app F)
    (F : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) b).map (δ.hom.app F) ≫
      (baseChangeMap (ModuleCat.{u + 1} Λ) sp.toCommSq).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj F) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) p₁).map
        ((@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} Λ) sk)).inv.app F) =
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} Λ) si)).inv.app
        ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).map
        ((baseChangeMap (ModuleCat.{u + 1} Λ) sr.toCommSq).app F) ≫
      δ₁.hom.app ((upperStar (ModuleCat.{u + 1} Λ) d).obj F) := by
  let sq : CommSq d (k₁ ≫ p₁) (k ≫ p) b := ⟨by
    rw [← Category.assoc, sk.w, Category.assoc, sp.w, Category.assoc]⟩
  have ht := ordinaryBaseChange_comp Λ k p k₁ p₁ d a b sk.toCommSq sp.toCommSq
    (k ≫ p) (k₁ ≫ p₁) rfl rfl sq F
  have hb := ordinaryBaseChange_comp Λ r i r₁ i₁ d c b sr.toCommSq si.toCommSq
    (k ≫ p) (k₁ ≫ p₁) h h₁ sq F
  have := mono_ordinaryOpenInclusion Λ k₁ ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)
  apply (cancel_mono ((lowerStar (ModuleCat.{u + 1} Λ) p₁).map
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k₁).app
        ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) k₁ p₁).hom.app
        ((upperStar (ModuleCat.{u + 1} Λ) d).obj F))).1
  simp only [Category.assoc]
  rw [hδ₁, ← Functor.map_comp_assoc, ordinaryOpenBaseChange_inclusion Λ k k₁ d a sk F]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (baseChangeMap (ModuleCat.{u + 1} Λ) sp.toCommSq).naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn,
    ← ht, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hδ]
  have he := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i₁).naturality
    ((baseChangeMap (ModuleCat.{u + 1} Λ) sr.toCommSq).app F)
  rw [reassoc_of% he, ← Category.assoc,
    ordinaryOpenBaseChange_inclusion Λ i i₁ c b si]
  simp only [Category.assoc]
  rw [← hb, ← Functor.map_comp_assoc]

private theorem derivedNatIso_symm
    {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    {F G : B ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryPlusNatIso e.symm =
      (Functor.mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Functor.mapDerivedCategoryPlusNatIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.fullyFaithfulCancelRight_inv_app,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, NatTrans.comp_app, Category.assoc]
  rfl

private theorem genericBaseChange_eq (Λ : Type (u + 1)) [CommRing Λ]
    {X Y X₁ Y₁ : Scheme.{u}} {f : X ⟶ Y} {f₁ : X₁ ⟶ Y₁}
    {a : X₁ ⟶ X} {b : Y₁ ⟶ Y} (sq : CommSq a f₁ f b) :
    Functor.rightDerivedFunctorPlusBaseChange (baseChangeMap (ModuleCat.{u + 1} Λ) sq) =
      derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq := by
  rfl

/-- Source: Stacks Project, More on Étale Cohomology, Tag 0F7F.

Proof: Write βk and βi for the inverses of the ordinary extension-by-zero
base-change mates. Their composites with the inclusions into direct images
are the ordinary base-change maps composed with the original inclusions.
Postcompose the proposed ordinary cube with p₁* of the inclusion k₁! → k₁*
and the lowerStar compositor. This is monic. Substitute the normalization of δ
on the original and pulled-back squares. Pasting of ordinary base-change maps
then makes the two composites equal, so the ordinary cube commutes.
Apply rightDerivedFunctorPlusBaseChange_cube with G=r*, H=p*, G₀=r₁*, H₀=p₁*,
P=k!, Q=i!, P₀=k₁!, Q₀=i₁!, and transverse maps d*, c*, a*, b*.
The four transverse functors and the four extension-by-zero functors are exact;
no preservation of injectives by inverse image is required. The two remaining
faces are the ordinary module base-change maps, whose right derived lifts are
derivedBaseChangeMapPlus by their unit factorization and uniqueness. The exact
derived lifts of βk and βi are extensionZeroBaseChangeDerivedPlusIso by its
definition. Substituting these identifications into the generic derived cube
gives the asserted equation, with all composition isomorphisms in the displayed
order. This argument allows arbitrary b, including empty fibres.
(blueprint: lem-cbc-proper-open-interchange-base-change). -/
theorem properOpenInterchange_baseChange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
    (hδ : (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
      [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F)) :
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ {A₁ B₁ C₁ D₁ :
        Scheme.{u}}
      (a : B₁ ⟶ B) (b : D₁ ⟶ D) (c : C₁ ⟶ C) (d : A₁ ⟶ A)
      (k₁ : A₁ ⟶ B₁) (i₁ : C₁ ⟶ D₁) (r₁ : A₁ ⟶ C₁) (p₁ : B₁ ⟶ D₁)
      [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
      (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sr : IsPullback d r₁ r c) (sp : IsPullback a p₁ p b)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange (δ k i r p h).hom).app K) ≫
        (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sp.toCommSq).app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₁).map
        ((extensionZeroBaseChangeDerivedPlusIso Λ sk).hom.app K) =
      (extensionZeroBaseChangeDerivedPlusIso Λ si).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u
        + 1} Λ) r).obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sr.toCommSq).app K) ≫
        (Functor.rightDerivedFunctorPlusBaseChange (δ k₁ i₁ r₁ p₁ h₁).hom).app ((upperStar
          (ModuleCat.{u + 1} Λ) d).mapDerivedCategoryPlus.obj
        K)) := by
  intro A B C D k i r p _ _ _ _ h A₁ B₁ C₁ D₁ a b c d k₁ i₁ r₁ p₁ _ _ _ _ h₁
    sk si sr sp K
  let ck := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sk)
  let ci := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) si)
  have hc := Functor.rightDerivedFunctorPlusBaseChange_cube
    (lowerStar (ModuleCat.{u + 1} Λ) r) (lowerStar (ModuleCat.{u + 1} Λ) p)
    (lowerStar (ModuleCat.{u + 1} Λ) r₁) (lowerStar (ModuleCat.{u + 1} Λ) p₁)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k₁)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁)
    (upperStar (ModuleCat.{u + 1} Λ) d) (upperStar (ModuleCat.{u + 1} Λ) c)
    (upperStar (ModuleCat.{u + 1} Λ) a) (upperStar (ModuleCat.{u + 1} Λ) b)
    (δ k i r p h).hom (δ k₁ i₁ r₁ p₁ h₁).hom
    (baseChangeMap (ModuleCat.{u + 1} Λ) sr.toCommSq)
    (baseChangeMap (ModuleCat.{u + 1} Λ) sp.toCommSq) ci ck
    (ordinaryInterchange_cube Λ k i r p h a b c d k₁ i₁ r₁ p₁ h₁ sk si sr sp
      (δ k i r p h) (δ k₁ i₁ r₁ p₁ h₁) (hδ k i r p h) (hδ k₁ i₁ r₁ p₁ h₁)) K
  simp only [genericBaseChange_eq] at hc
  simpa only [rightDerivedLowerStarPlus,
    extensionZeroBaseChangeDerivedPlusIso, derivedNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc, ck, ci] using hc

end AlgebraicGeometry.Etale
