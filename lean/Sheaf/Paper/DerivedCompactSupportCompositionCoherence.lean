/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence

/-!
# Structural coherence for three proper images and three open extensions

Source: Stacks Project, More on Étale Cohomology, Tag 0F7K, proof of
`lemma-pseudo-functor`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private lemma derived_triangle_assoc
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
    (FG : C₀ ⥤ C₂) (GH : C₁ ⥤ C₃) (FGH : C₀ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [FG.Additive] [GH.Additive] [FGH.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (eFG : FG ≅ F ⋙ G) (eGH : GH ≅ G ⋙ H)
    (eF_GH : FGH ≅ F ⋙ GH) (eFG_H : FGH ≅ FG ⋙ H)
    (h : eF_GH ≪≫ Functor.isoWhiskerLeft F eGH =
      eFG_H ≪≫ Functor.isoWhiskerRight eFG H) :
    (Functor.mapDerivedCategoryTriangleIso eF_GH).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryTriangleIso eGH).hom =
      (Functor.mapDerivedCategoryTriangleIso eFG_H).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eFG).hom
          H.mapDerivedCategory := by
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F GH).hom,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerLeft,
    Category.assoc, ← Category.assoc (Functor.mapDerivedCategoryCompIso FG H).hom,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerRight]
  simp only [← Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_trans, h,
    Functor.mapDerivedCategoryNatIso_trans]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_assoc]

private lemma conjugate_triangle_assoc
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₃}
    {FG : C₀ ⥤ C₂} {GH : C₁ ⥤ C₃} {FGH : C₀ ⥤ C₃}
    {RF : C₁ ⥤ C₀} {RG : C₂ ⥤ C₁} {RH : C₃ ⥤ C₂}
    {RFG : C₂ ⥤ C₀} {RGH : C₃ ⥤ C₁} {RFGH : C₃ ⥤ C₀}
    (af : F ⊣ RF) (ag : G ⊣ RG) (ah : H ⊣ RH)
    (afg : FG ⊣ RFG) (agh : GH ⊣ RGH) (afgh : FGH ⊣ RFGH)
    (eFG : FG ≅ F ⋙ G) (eGH : GH ≅ G ⋙ H)
    (eF_GH : FGH ≅ F ⋙ GH) (eFG_H : FGH ≅ FG ⋙ H)
    (h : eF_GH.hom ≫ Functor.whiskerLeft F eGH.hom =
      eFG_H.hom ≫ Functor.whiskerRight eFG.hom H) :
    Functor.whiskerLeft RH (conjugateEquiv (af.comp ag) afg eFG.hom) ≫
        conjugateEquiv (afg.comp ah) afgh eFG_H.hom =
      Functor.whiskerRight (conjugateEquiv (ag.comp ah) agh eGH.hom) RF ≫
        conjugateEquiv (af.comp agh) afgh eF_GH.hom := by
  have hm : (Functor.associator RH RG RF).hom ≫
      (Functor.whiskerLeft RH (conjugateEquiv (af.comp ag) afg eFG.hom) ≫
        conjugateEquiv (afg.comp ah) afgh eFG_H.hom) =
      Functor.whiskerRight (conjugateEquiv (ag.comp ah) agh eGH.hom) RF ≫
        conjugateEquiv (af.comp agh) afgh eF_GH.hom := by
    rw [← conjugateEquiv_associator_hom af ag ah,
      ← conjugateEquiv_whiskerRight (af.comp ag) afg ah,
      ← conjugateEquiv_whiskerLeft (ag.comp ah) agh af,
      conjugateEquiv_comp, conjugateEquiv_comp, conjugateEquiv_comp]
    congr 1
    apply NatTrans.ext
    funext K
    simpa only [NatTrans.comp_app, Functor.associator_hom_app, Category.comp_id] using
      (NatTrans.congr_app h K).symm
  apply NatTrans.ext
  funext K
  simpa only [NatTrans.comp_app, Functor.associator_hom_app, Category.id_comp] using
    NatTrans.congr_app hm K

private lemma derived_triangle_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H H' : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [H'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (h : H = H') (e : H' ≅ F ⋙ G) :
    Functor.mapDerivedCategoryTriangleIso (eqToIso h ≪≫ e) =
      eqToIso (by subst h; rfl) ≪≫
        Functor.mapDerivedCategoryTriangleIso e := by
  subst h
  apply Iso.ext
  simp [Functor.mapDerivedCategoryTriangleIso]

@[reassoc] private lemma image_transport
    {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (h : F = G) {M N N' : C} (e : N = N') (f : M ⟶ N) :
    (eqToHom h).app M ≫ G.map f ≫ eqToHom (by subst h; subst e; rfl) =
      F.map (f ≫ eqToHom e) := by
  subst h
  subst e
  simp

namespace AlgebraicGeometry.Etale

private lemma open_derived_assoc
    (A : Type (u + 1)) [CommRing A]
    {X U V W : Scheme.{u}} (l : X ⟶ U) (a : U ⟶ V) (b : V ⟶ W)
    [IsOpenImmersion l] [IsOpenImmersion a] [IsOpenImmersion b] :
    (Functor.mapDerivedCategoryTriangleIso
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l (a ≫ b))).hom ≫
        Functor.whiskerLeft D((l)_!open[ModuleCat.{u + 1} A])
          (Functor.mapDerivedCategoryTriangleIso
            (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b)).hom =
      (eqToIso (by simp only [Category.assoc])).hom ≫
      (Functor.mapDerivedCategoryTriangleIso
        (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) (l ≫ a) b)).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a)).hom
            D((b)_!open[ModuleCat.{u + 1} A]) := by
  let O := fun {S T : Scheme.{u}} (j : S ⟶ T) [IsOpenImmersion j] ↦
    (j)_!open[ModuleCat.{u + 1} A]
  have h : openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l (a ≫ b) ≪≫
        Functor.isoWhiskerLeft (O l)
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b) =
      (eqToIso (by simp only [Category.assoc]) ≪≫
        openImmersionLowerShriekComp (ModuleCat.{u + 1} A) (l ≫ a) b) ≪≫
        Functor.isoWhiskerRight
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a) (O b) := by
    apply Iso.ext_inv
    apply NatTrans.ext
    funext F
    simpa [O] using
      ((openImmersionLowerShriekComp_coherence A).2.2 l a b F).symm
  have hd := derived_triangle_assoc (O l) (O a) (O b) (O (l ≫ a)) (O (a ≫ b))
    (O (l ≫ a ≫ b))
    (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a)
    (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b)
    (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l (a ≫ b))
    (eqToIso (by simp only [O, Category.assoc]) ≪≫
      openImmersionLowerShriekComp (ModuleCat.{u + 1} A) (l ≫ a) b) h
  rw [derived_triangle_transport] at hd
  simpa only [Iso.trans_hom, Category.assoc] using hd

private lemma push_comp_of_eq
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    conjugateEquiv
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) fg)
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg)).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).hom ≫
        eqToHom (by subst hfg; rfl) := by
  subst hfg
  rw [eqToHom_refl, Category.comp_id]
  rfl

private lemma push_derived_assoc
    (A : Type (u + 1)) [CommRing A]
    {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ Z) (t : Z ⟶ T) :
    Functor.whiskerLeft R((p)_*[ModuleCat.{u + 1} A])
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s t).hom ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p (s ≫ t)).hom =
    Functor.whiskerRight
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom
          R((t)_*[ModuleCat.{u + 1} A]) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (p ≫ s) t).hom ≫
        eqToHom (by simp only [Category.assoc]) := by
  let B := ModuleCat.{u + 1} A
  have hu : upperStarComp B (p ≫ s) t (p ≫ s ≫ t)
        (Category.assoc p s t).symm ≪≫
        Functor.isoWhiskerLeft (t)^*[B] (upperStarComp B p s) =
      upperStarComp B p (s ≫ t) ≪≫
        Functor.isoWhiskerRight (upperStarComp B s t) (p)^*[B] := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Category.comp_id] using
      (NatTrans.congr_app (congrArg Iso.hom (upperStarComp_assoc B p s t)) M).symm
  have hd := derived_triangle_assoc (t)^*[B] (s)^*[B] (p)^*[B]
    (s ≫ t)^*[B] (p ≫ s)^*[B] (p ≫ s ≫ t)^*[B]
    (upperStarComp B s t) (upperStarComp B p s)
    (upperStarComp B (p ≫ s) t (p ≫ s ≫ t) (Category.assoc p s t).symm)
    (upperStarComp B p (s ≫ t)) hu
  have hm := conjugate_triangle_assoc
    (mapDerivedUpperStarLowerStarAdjunction B t)
    (mapDerivedUpperStarLowerStarAdjunction B s)
    (mapDerivedUpperStarLowerStarAdjunction B p)
    (mapDerivedUpperStarLowerStarAdjunction B (s ≫ t))
    (mapDerivedUpperStarLowerStarAdjunction B (p ≫ s))
    (mapDerivedUpperStarLowerStarAdjunction B (p ≫ s ≫ t))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp B s t))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp B p s))
    (Functor.mapDerivedCategoryTriangleIso
      (upperStarComp B (p ≫ s) t (p ≫ s ≫ t) (Category.assoc p s t).symm))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp B p (s ≫ t))) hd
  rw [push_comp_of_eq A, push_comp_of_eq A, push_comp_of_eq A,
    push_comp_of_eq A] at hm
  simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using hm

attribute [local irreducible] rightDerivedLowerStarComp
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  openImmersionLowerShriekComp Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek

/-- The structural loop comparing the two parenthesizations of three proper direct
images and three open extensions is the identity. No proper/open interchange is involved.
Source: Stacks Project, Tag 0F7K, proof of `lemma-pseudo-functor`, structural
identifications of the common target; Tag 0D6E for derived direct-image composition
(blueprint: lem-amb-derived-compact-support-composition-coherence).

Proof: The two open-extension contraction maps agree by the three-fold clause of
`openImmersionLowerShriekComp_coherence`. Apply the exact functor construction on derived
categories to this equality. Naturality of `mapDerivedCategoryCompIso` in both factors and
its associativity identify the resulting equality with the displayed open comparisons.
For direct images, `rightDerivedLowerStarComp` is the conjugate of the analogous exact
pullback comparison. The associativity of `upperStarComp`, lifted to derived categories
by the same exact-functor coherence, implies the associativity of these conjugates by
`conjugateEquiv_comp`, its whiskering identities, and its associator identity. Thus the
initial two direct-image comparisons cancel the inverse comparisons at the end, after
transport along scheme associativity. Move the open comparisons through these natural
transformations. The open-extension coherence just obtained then cancels the remaining
open comparisons. Functoriality and the hom/inverse identities leave the identity map.
The transports express only associativity of scheme composition. The argument works
for arbitrary schemes and arbitrary commutative coefficients; in particular it does not
require cartesian squares, properness, Noetherianity, or finiteness of the coefficients. -/
theorem derivedCompactSupportComposition_cancel
    (A : Type (u + 1)) [CommRing A]
    {X U V Xbar Ybar Zbar T : Scheme.{u}}
    (l : X ⟶ U) (a : U ⟶ V) (b : V ⟶ Xbar)
    (p : Xbar ⟶ Ybar) (s : Ybar ⟶ Zbar) (t : Zbar ⟶ T)
    [IsOpenImmersion l] [IsOpenImmersion a] [IsOpenImmersion b]
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s t).hom.app
        (R((p)_*[ModuleCat.{u + 1} A]).obj
          (D((b)_!open[ModuleCat.{u + 1} A]).obj
            (D((a)_!open[ModuleCat.{u + 1} A]).obj
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))) ≫
      R((s ≫ t)_*[ModuleCat.{u + 1} A]).map
        (R((p)_*[ModuleCat.{u + 1} A]).map
          ((Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).inv.app
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K))) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p (s ≫ t)).hom.app
        (D((a ≫ b)_!open[ModuleCat.{u + 1} A]).obj
          (D((l)_!open[ModuleCat.{u + 1} A]).obj K)) ≫
      R((p ≫ s ≫ t)_*[ModuleCat.{u + 1} A]).map
        ((Functor.mapDerivedCategoryNatIso
            (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l (a ≫ b)) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).inv.app K) ≫
      eqToHom (by simp only [Category.assoc]) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (p ≫ s) t).inv.app _ ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).inv.app _) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        (R((s)_*[ModuleCat.{u + 1} A]).map
          (R((p)_*[ModuleCat.{u + 1} A]).map
            ((Functor.mapDerivedCategoryNatIso
                (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) (l ≫ a) b) ≪≫
              Functor.mapDerivedCategoryCompIso _ _).hom.app K ≫
              D((b)_!open[ModuleCat.{u + 1} A]).map
                ((Functor.mapDerivedCategoryNatIso
                    (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a) ≪≫
                  Functor.mapDerivedCategoryCompIso _ _).hom.app K)))) = 𝟙 _ := by
  have hp := NatTrans.congr_app (push_derived_assoc A p s t)
    (D((b)_!open[ModuleCat.{u + 1} A]).obj
      (D((a)_!open[ModuleCat.{u + 1} A]).obj
        (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))
  have ho := NatTrans.congr_app (open_derived_assoc A l a b) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj] at hp ho
  have hn := (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p (s ≫ t)).hom.naturality
    ((Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).inv.app
          (D((l)_!open[ModuleCat.{u + 1} A]).obj K))
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% hp]
  rw [← Functor.map_comp_assoc,
    image_transport_assoc (e := by simp only [Category.assoc])]
  rw [← (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (p ≫ s) t).hom.naturality_assoc]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp]
  rw [← (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom.naturality_assoc]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp, Category.assoc]
  simp only [Functor.mapDerivedCategoryTriangleIso, eqToIso.hom,
    eqToHom_app] at ho
  rw [← ho]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  simp

end AlgebraicGeometry.Etale
