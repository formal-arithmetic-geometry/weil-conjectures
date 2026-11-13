/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeCodomainIso
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeDomainIso
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Transport of the derived mate in its base coordinates

Source: Stacks Project, Tags 08HY, 0D5S and 0D5T.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- Change the two base schemes, keeping the upper-left scheme fixed.
Source: Stacks Project, Tag 08HY (counit description), Tags 0D5S and 0D5T. -/
theorem exists_derivedBaseChange_base_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B)
    (hA : g' ≫ (f ≫ eS.hom) =
      (f' ≫ eT.hom) ≫ (eT.inv ≫ g ≫ eS.hom)) :
    let fA := f ≫ eS.hom
    let gA := eT.inv ≫ g ≫ eS.hom
    let T := schemeDerivedDirectImage eT.inv
    ∃ b : schemeDerivedDirectImage f' ≅
        schemeDerivedDirectImage (f' ≫ eT.hom) ⋙ T,
    ∃ a : schemeDerivedDirectImage f ⋙ derivedPullback g ≅
        schemeDerivedDirectImage fA ⋙ derivedPullback gA ⋙ T,
      ∀ E : schemeDerivedCategory X,
        schemeDerivedBaseChangeMap f f' g g' h E ≫
            b.hom.app ((derivedPullback g').obj E) =
          a.hom.app E ≫ T.map
            (schemeDerivedBaseChangeMap fA (f' ≫ eT.hom) gA g' hA E) := by
  have hS : g' ≫ (f ≫ eS.hom) = f' ≫ (g ≫ eS.hom) := by
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ eS.hom) h
  obtain ⟨aS, haS⟩ := exists_derivedBaseChange_codomain_iso f g g' f' h eS hS
  obtain ⟨b, aT, haT⟩ := exists_derivedBaseChange_domain_iso
    (f ≫ eS.hom) (g ≫ eS.hom) g' f' hS eT hA
  refine ⟨b, aS ≪≫ aT, ?_⟩
  intro E
  calc
    _ = (aS.hom.app E ≫
        schemeDerivedBaseChangeMap (f ≫ eS.hom) f' (g ≫ eS.hom) g' hS E) ≫
        b.hom.app ((derivedPullback g').obj E) := by rw [haS E]
    _ = aS.hom.app E ≫ (aT.hom.app E ≫ (schemeDerivedDirectImage eT.inv).map
        (schemeDerivedBaseChangeMap (f ≫ eS.hom) (f' ≫ eT.hom)
          (eT.inv ≫ g ≫ eS.hom) g' hA E)) := by
      rw [Category.assoc, haT E]
    _ = _ := by simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]


end AlgebraicGeometry
