/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver

/-!
# Naturality of internal Hom under restriction

## References

* Stacks Project, Modules on Sites, Sections 04TT (internal Hom) and 04IX (localization); this is
  the sectionwise comparison underlying Cohomology, Tag 08DL
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the internal Hom restriction isomorphism in both arguments. -/
theorem overHomObjIso_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}} (U : C)
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (f : A' ⟶ A) (g : B ⟶ B') :
    (SheafOfModules.overFunctor _ U).map
        (SheafOfModules.homObjMap (R := R) f g) ≫
          (SheafOfModules.overHomObjIso A' B' U).hom =
      (SheafOfModules.overHomObjIso A B U).hom ≫
        SheafOfModules.homObjMap (R := R.over U)
          ((SheafOfModules.overFunctor _ U).map f)
          ((SheafOfModules.overFunctor _ U).map g) := by
  apply SheafOfModules.hom_ext
  simp only [SheafOfModules.comp_val, SheafOfModules.overHomObjIso,
    Functor.FullyFaithful.preimageIso_hom, SheafOfModules.fullyFaithfulForget,
    Iso.trans_hom, Iso.refl_hom]
  have he (P Q : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
      (eqToIso (SheafOfModules.homObj_restrictOver_eq P Q U)).hom =
        𝟙 (PresheafOfModules.homObj (R := (Over.forget U).op ⋙ R.obj)
          (P.over U).val (Q.over U).val) := by
    exact eqToHom_refl
      (PresheafOfModules.homObj (R := (Over.forget U).op ⋙ R.obj)
        (P.over U).val (Q.over U).val)
      (SheafOfModules.homObj_restrictOver_eq P Q U)
  rw [he, he]
  ext W φ : 3
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  rfl

end CategoryTheory
