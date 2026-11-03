/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SystemDirectImageLeftUnit

/-! # The normalized whole-system support refinement

Source: Stacks 0F7B and 07A7, normalization of the proper/open mate.
(blueprint: lem-pur-system-support-refinement-unit). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.proofsInPublic true
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions _root_.instCategoryDerivedCategory
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)

/-- Component-normalized pasting of an identity comparison and a compositor.
Source: Stacks 07A7; naturality of whiskering and associators.
(blueprint: lem-pur-system-support-refinement-unit). -/
def normalizedSupportPaste
    {A B D S : Type*} [Category A] [Category B] [Category D] [Category S]
    (F : A ⥤ A) (Jd : A ⥤ S) (Jc : A ⥤ B) (Rp : B ⥤ S)
    (Rh : S ⥤ D) (Rg : B ⥤ D) (e : F ≅ 𝟭 A)
    (a : F ⋙ Jd ⟶ Jc ⋙ Rp) (b : Rp ⋙ Rh ≅ Rg) :
    Jd ⋙ Rh ⟶ Jc ⋙ Rg where
  app M := Rh.map (Jd.map (e.inv.app M) ≫ a.app M) ≫ b.hom.app (Jc.obj M)
  naturality {M N} v := by
    have h := (Functor.whiskerRight
        ((Functor.leftUnitor Jd).inv ≫ Functor.whiskerRight e.inv Jd ≫ a) Rh ≫
      (Functor.associator Jc Rp Rh).hom ≫ Functor.whiskerLeft Jc b.hom).naturality v
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.leftUnitor_inv_app, Category.id_comp] using h

/-- The component equation for the normalized paste.
Source: Stacks 07A7; the component definition above.
(blueprint: lem-pur-system-support-refinement-unit). -/
theorem normalizedSupportPaste_app
    {A B D S : Type*} [Category A] [Category B] [Category D] [Category S]
    (F : A ⥤ A) (Jd : A ⥤ S) (Jc : A ⥤ B) (Rp : B ⥤ S)
    (Rh : S ⥤ D) (Rg : B ⥤ D) (e : F ≅ 𝟭 A)
    (a : F ⋙ Jd ⟶ Jc ⋙ Rp) (b : Rp ⋙ Rh ≅ Rg) (M : A) :
    (normalizedSupportPaste F Jd Jc Rp Rh Rg e a b).app M =
      Rh.map (Jd.map (e.inv.app M) ≫ a.app M) ≫ b.hom.app (Jc.obj M) := rfl

attribute [irreducible] normalizedSupportPaste

/-- The open-identity-normalized mate pasted with the proper compositor.
Source: Stacks 0F7B and 07A7.
(blueprint: lem-pur-system-support-refinement-unit). -/
def canonicalSupportRefinement {X Y Z W : Scheme.{u}}
    (j : X ⟶ Z) (g : Z ⟶ Y) (i : X ⟶ W) (h : W ⟶ Y) (p : Z ⟶ W)
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i] [IsProper p]
    [IsProper (𝟙 X)] (hj : j ≫ p = (𝟙 X) ≫ i)
    (hg : R C τ (p ≫ h) = R C τ g) :
    J C τ i ⋙ R C τ h ⟶ J C τ j ⋙ R C τ g :=
  normalizedSupportPaste (R C τ (𝟙 X)) (J C τ i) (J C τ j) (R C τ p)
    (R C τ h) (R C τ g) (sId C τ X)
    (gamma C τ j (𝟙 X) p i hj)
    (sComp C τ p h ≪≫ eqToIso hg)

/-- Identity refinement acts by the identity on every whole-system object.
Source: Stacks 0F7B and 07A7.
(blueprint: lem-pur-system-support-refinement-unit).
Proof: the proper compositor with an identity factor is R(g) applied to sId(Z).
Functoriality combines it with the mate; gamma's identity normalization then
identifies the result with J(j) applied to sId(X). The initial inverse sId(X)
cancels it. This argument works for every object, including the zero object. -/
theorem canonicalSupportRefinement_id_app {X Y Z : Scheme.{u}}
    (j : X ⟶ Z) (g : Z ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [IsProper (𝟙 X)] [IsProper (𝟙 Z)]
    (M : Derived C τ X)
    (hgamma : ∀ N : Derived C τ X,
      (gamma C τ j (𝟙 X) (𝟙 Z) j (by simp)).app N ≫
        (sId C τ Z).hom.app ((J C τ j).obj N) =
          (J C τ j).map ((sId C τ X).hom.app N)) :
    (canonicalSupportRefinement C τ j g j g (𝟙 Z) (by simp)
      (congrArg (R C τ) (Category.id_comp g))).app M = 𝟙 _ := by
  delta canonicalSupportRefinement
  rw [normalizedSupportPaste_app]
  have hu := sComp_left_unit C τ g ((J C τ j).obj M)
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [hu, ← Functor.map_comp, Category.assoc, hgamma, ← Functor.map_comp]
  rw [Iso.inv_hom_id_app]
  exact (congrArg (R C τ g).map ((J C τ j).map_id M)).trans
    ((R C τ g).map_id ((J C τ j).obj M))

/-- Identity refinement acts by the identity on every whole-system object.
Source: Stacks 0F7B and 07A7.
(blueprint: lem-pur-system-support-refinement-unit).
Proof: the proper compositor with an identity factor is R(g) applied to sId(Z).
Functoriality combines it with the mate; gamma's identity normalization then
identifies the result with J(j) applied to sId(X). The initial inverse sId(X)
cancels it. This argument works for every object, including the zero object. -/
theorem canonicalSupportRefinement_id {X Y Z : Scheme.{u}}
    (j : X ⟶ Z) (g : Z ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [IsProper (𝟙 X)] [IsProper (𝟙 Z)]
    (hgamma : ∀ N : Derived C τ X,
      (gamma C τ j (𝟙 X) (𝟙 Z) j (by simp)).app N ≫
        (sId C τ Z).hom.app ((J C τ j).obj N) =
          (J C τ j).map ((sId C τ X).hom.app N)) :
    canonicalSupportRefinement C τ j g j g (𝟙 Z) (by simp)
      (congrArg (R C τ) (Category.id_comp g)) = 𝟙 (J C τ j ⋙ R C τ g) := by
  apply NatTrans.ext
  funext M
  exact canonicalSupportRefinement_id_app C τ j g M hgamma

attribute [local irreducible] J R gamma sComp sId

/-- The support comparison, with identity refinements computed as identity maps.
Source: Stacks 0F7B, identity normalization of the proper/open mate.
(blueprint: lem-pur-system-support-refinement-unit).
The construction uses the canonical mate paste except when the two presentations
and the refinement morphism are literally equal to an identity presentation. -/
def supportRefinement {X Y Z W : Scheme.{u}}
    (j : X ⟶ Z) (g : Z ⟶ Y) (i : X ⟶ W) (h : W ⟶ Y) (p : Z ⟶ W)
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i] [IsProper p]
    [IsProper (𝟙 X)] (hj : j ≫ p = (𝟙 X) ≫ i)
    (hg : R C τ (p ≫ h) = R C τ g) :
    J C τ i ⋙ R C τ h ⟶ J C τ j ⋙ R C τ g := by
  classical
  by_cases e : W = Z
  · subst W
    by_cases ei : i = j
    · subst i
      by_cases eh : h = g
      · subst h
        by_cases ep : p = 𝟙 Z
        · exact 𝟙 _
        · exact canonicalSupportRefinement C τ j g j g p hj hg
      · exact canonicalSupportRefinement C τ j g j h p hj hg
    · exact canonicalSupportRefinement C τ j g i h p hj hg
  · exact canonicalSupportRefinement C τ j g i h p hj hg

/-- Computing the identity case preserves the canonical mate paste.
Source: Stacks 0F7B and 07A7.
(blueprint: lem-pur-system-support-refinement-unit).
Proof: outside the identity case this is the definition. In the identity case,
apply the component calculation above with gamma_identities, then extensionality.
Proof irrelevance identifies the specified square and functor equality proofs. -/
theorem supportRefinement_eq_canonical {X Y Z W : Scheme.{u}}
    (j : X ⟶ Z) (g : Z ⟶ Y) (i : X ⟶ W) (h : W ⟶ Y) (p : Z ⟶ W)
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i] [IsProper p]
    [IsProper (𝟙 X)] (hj : j ≫ p = (𝟙 X) ≫ i)
    (hg : R C τ (p ≫ h) = R C τ g) :
    supportRefinement C τ j g i h p hj hg =
      canonicalSupportRefinement C τ j g i h p hj hg := by
  classical
  unfold supportRefinement
  split
  · rename_i e
    subst W
    dsimp only
    split
    · rename_i ei
      subst i
      dsimp only
      split
      · rename_i eh
        subst h
        dsimp only
        split
        · rename_i ep
          subst p
          exact (canonicalSupportRefinement_id C τ j g
            ((gamma_identities C τ).1 j (by simp))).symm
        · rfl
      · rfl
    · rfl
  · rfl

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
