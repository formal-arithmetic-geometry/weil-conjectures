/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting

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

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
