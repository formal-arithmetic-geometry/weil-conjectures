/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom

/-!
# The internal hom of sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)`. For sheaves of modules `M` and `N`
over `R`, we define the sheaf of modules `SheafOfModules.homObj M N`, whose underlying presheaf
is the internal hom presheaf `PresheafOfModules.homObj M.val N.val`.

The sheaf condition is `PresheafOfModules.isSheaf_homObj`: if `N` is a sheaf, then so is
`homObj M N`. The underlying presheaf of types of `homObj M N` identifies with the subpresheaf
of `presheafHom M.presheaf N.presheaf` of `R`-linear morphisms (`linearSubfunctor`). The
presheaf `presheafHom M.presheaf N.presheaf` is a sheaf by `Presheaf.IsSheaf.hom`, and
`R`-linearity is a local condition because `N` is separated.

## Main definitions and results

* `PresheafOfModules.isSheaf_homObj`: `homObj M N` is a sheaf if `N` is.
* `SheafOfModules.homObj M N`: the internal hom sheaf `U ↦ Hom_{R|_U}(M|_U, N|_U)`.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Cᵒᵖ ⥤ CommRingCat.{u}} (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))

/-- The subpresheaf of `presheafHom M.presheaf N.presheaf` consisting of the `R`-linear
morphisms. -/
def linearSubfunctor : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := {α | ∀ (W : (Over U.unop)ᵒᵖ) (r : (R ⋙ forget₂ CommRingCat RingCat).obj (op W.unop.left))
    (m : M.obj (op W.unop.left)),
      α.app W (r • m) = r • show N.obj (op W.unop.left) from α.app W m}
  map f _ hα W r m := hα (op ((Over.map f.unop).obj W.unop)) r m

variable {M N} in
lemma mem_linearSubfunctor_obj {U : Cᵒᵖ} (α : (presheafHom M.presheaf N.presheaf).obj U) :
    α ∈ (linearSubfunctor M N).obj U ↔
      ∀ (W : (Over U.unop)ᵒᵖ) (r : (R ⋙ forget₂ CommRingCat RingCat).obj (op W.unop.left))
        (m : M.obj (op W.unop.left)),
        α.app W (r • m) = r • show N.obj (op W.unop.left) from α.app W m :=
  Iff.rfl

/-- The underlying presheaf of types of `homObj M N` is the subpresheaf of `R`-linear morphisms
of `presheafHom M.presheaf N.presheaf`. -/
noncomputable def homObjCompForgetIso :
    (homObj M N).presheaf ⋙ forget _ ≅ (linearSubfunctor M N).toFunctor :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun φ := ⟨(toPresheaf _).map φ,
        (mem_linearSubfunctor_obj _).2 fun W r m ↦ (φ.app W).hom.map_smul r m⟩
      invFun α := homMk α.1 fun W r m ↦ (mem_linearSubfunctor_obj _).1 α.2 W r m
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ ↦ rfl)

variable {M N} in
/-- The internal hom `homObj M N` is a sheaf if `N` is a sheaf. -/
theorem isSheaf_homObj (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (homObj M N).presheaf := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{max u₁ v₁ v}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_iso J (homObjCompForgetIso M N).symm ?_
  have hH := Presheaf.IsSheaf.hom M.presheaf N.presheaf hN
  rw [isSheaf_iff_isSheaf_of_type] at hH
  have hN' : Presieve.IsSheaf J (N.presheaf ⋙ forget _) := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf J _ (forget _) hN)
  refine (Subfunctor.isSheaf_iff _ hH).2 fun U α hα ↦ (mem_linearSubfunctor_obj _).2 ?_
  intro W r m
  refine (hN' _ (J.pullback_stable W.unop.hom hα)).isSeparatedFor.ext fun Z h hh ↦ ?_
  have H := (mem_linearSubfunctor_obj _).1 hh (op (Over.mk (𝟙 Z))) (R.map h.op r)
    (M.map h.op m)
  let β := ((presheafHom M.presheaf N.presheaf).map (h ≫ W.unop.hom).op α).app
    (op (Over.mk (𝟙 Z)))
  have nat (x : M.obj (op W.unop.left)) : N.map h.op (α.app W x) = β (M.map h.op x) :=
    (ConcreteCategory.congr_hom
      (α.naturality (Over.homMk h : Over.mk (h ≫ W.unop.hom) ⟶ W.unop).op) x).symm.trans
      (ConcreteCategory.congr_hom
        (presheafHom_map_app (𝟙 Z) (h ≫ W.unop.hom) _ (Category.id_comp _) α) _).symm
  exact (nat (r • m)).trans ((congrArg β (M.map_smul h.op r m)).trans (H.trans
    ((congrArg (R.map h.op r • ·) (nat m).symm).trans (N.map_smul h.op r _).symm)))

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R : Sheaf J CommRingCat.{u}}
  (M N : SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))

/-- The internal hom sheaf of modules `U ↦ Hom_{R|_U}(M|_U, N|_U)`. -/
@[simps]
noncomputable def homObj :
    SheafOfModules.{max u₁ v₁ v} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) where
  val := PresheafOfModules.homObj (R := R.obj) M.val N.val
  isSheaf := PresheafOfModules.isSheaf_homObj N.isSheaf

end SheafOfModules
