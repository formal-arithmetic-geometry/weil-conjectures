/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Linear morphisms between restrictions of presheaves of modules

Let `R` be a presheaf of commutative rings on a site `(C, J)`, and let `M` and `N` be presheaves
of modules over `R`. A section over `U` of the presheaf of types `presheafHom M.presheaf N.presheaf`
is a morphism of abelian presheaves between the restrictions of `M` and `N` to `Over U`. Those
morphisms that are `R`-linear form a subpresheaf `presheafHomLinearSubfunctor M N`.

`R`-linearity is a local condition if `N` is separated, so this subpresheaf is a sheaf if `N` is
a sheaf, since `presheafHom M.presheaf N.presheaf` is then a sheaf by `Presheaf.IsSheaf.hom`.

## Main definitions and results

* `PresheafOfModules.presheafHomLinearSubfunctor M N`: the subpresheaf of `R`-linear morphisms
  of `presheafHom M.presheaf N.presheaf`.
* `PresheafOfModules.isSheaf_presheafHomLinearSubfunctor`: it is a sheaf if `N` is a sheaf.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Cᵒᵖ ⥤ CommRingCat.{u}} (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))

/-- The subpresheaf of `presheafHom M.presheaf N.presheaf` consisting of the `R`-linear
morphisms. -/
def presheafHomLinearSubfunctor : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := {α | ∀ (W : (Over U.unop)ᵒᵖ) (r : (R ⋙ forget₂ CommRingCat RingCat).obj (op W.unop.left))
    (m : M.obj (op W.unop.left)),
      α.app W (r • m) = r • show N.obj (op W.unop.left) from α.app W m}
  map f _ hα W r m := hα (op ((Over.map f.unop).obj W.unop)) r m

variable {M N} in
@[simp]
lemma mem_presheafHomLinearSubfunctor_obj {U : Cᵒᵖ}
    (α : (presheafHom M.presheaf N.presheaf).obj U) :
    α ∈ (presheafHomLinearSubfunctor M N).obj U ↔
      ∀ (W : (Over U.unop)ᵒᵖ) (r : (R ⋙ forget₂ CommRingCat RingCat).obj (op W.unop.left))
        (m : M.obj (op W.unop.left)),
        α.app W (r • m) = r • show N.obj (op W.unop.left) from α.app W m :=
  Iff.rfl

variable {M N} in
/-- `R`-linearity of a section of `presheafHom M.presheaf N.presheaf` is a local condition if
`N` is separated. -/
lemma mem_presheafHomLinearSubfunctor_obj_of_isSeparated
    (hN : Presieve.IsSeparated J (N.presheaf ⋙ forget _)) {U : Cᵒᵖ}
    (α : (presheafHom M.presheaf N.presheaf).obj U)
    (hα : (presheafHomLinearSubfunctor M N).sieveOfSection α ∈ J U.unop) :
    α ∈ (presheafHomLinearSubfunctor M N).obj U := by
  refine (mem_presheafHomLinearSubfunctor_obj _).2 fun W r m ↦ ?_
  -- As `N` is separated, it suffices to check the equality after restriction along every
  -- `h : Z ⟶ W.left` in the pullback along `W.hom` of the sieve on which `α` is linear.
  refine (hN _ (J.pullback_stable W.unop.hom hα)).ext fun Z h hh ↦ ?_
  -- The restriction `β` of `α` along `h ≫ W.hom`, evaluated at `Over.mk (𝟙 Z)`, is linear.
  let β : M.obj (op Z) → N.obj (op Z) :=
    ((presheafHom M.presheaf N.presheaf).map (h ≫ W.unop.hom).op α).app (op (Over.mk (𝟙 Z)))
  have hβ := (mem_presheafHomLinearSubfunctor_obj _).1 hh (op (Over.mk (𝟙 Z))) (R.map h.op r)
    (M.map h.op m)
  -- Restricting `α.app W` along `h` is `β` of the restriction:
  --   M(W.left) --α_W--> N(W.left)
  --      |                   |
  --    M(h)                N(h)
  --      v                   v
  --     M(Z) ------β----->  N(Z)
  have hnat (x : M.obj (op W.unop.left)) : N.map h.op (α.app W x) = β (M.map h.op x) :=
    ConcreteCategory.congr_hom (presheafHom_app_comp_map α W h) x
  -- Move `r` through `N(h)`, `β` and `M(h)`, using the linearity of `β`.
  -- `N(h) (α_W (r • m)) = β (M(h) (r • m)) = β (r|_Z • M(h) m) = r|_Z • β (M(h) m)`
  -- `= r|_Z • N(h) (α_W m) = N(h) (r • α_W m)`.
  exact (hnat (r • m)).trans <|
    (congrArg β (M.map_smul h.op r m)).trans <|
    hβ.trans <|
    (congrArg (R.map h.op r • ·) (hnat m).symm).trans <|
    (N.map_smul h.op r _).symm

variable {M N} in
/-- The presheaf of `R`-linear morphisms between restrictions of `M` and `N` is a sheaf if `N`
is a sheaf. -/
theorem isSheaf_presheafHomLinearSubfunctor (hN : Presheaf.IsSheaf J N.presheaf) :
    Presieve.IsSheaf J (presheafHomLinearSubfunctor M N).toFunctor := by
  have hH := Presheaf.IsSheaf.hom M.presheaf N.presheaf hN
  rw [isSheaf_iff_isSheaf_of_type] at hH
  have hN' : Presieve.IsSheaf J (N.presheaf ⋙ forget _) := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf J _ (forget _) hN)
  exact (Subfunctor.isSheaf_iff _ hH).2 fun _ α hα ↦
    mem_presheafHomLinearSubfunctor_obj_of_isSeparated hN'.isSeparated α hα

end PresheafOfModules
