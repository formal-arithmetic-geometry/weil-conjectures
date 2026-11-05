/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Ordinary global Hom-complex cohomology with independent site universes

Source: Stacks Project, Equation 0A8Z and Lemma 08JA.
(blueprint: lem-pur-hom-complex-global-homotopy)
-/

@[expose] public section

set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
namespace CategoryTheory

attribute [local irreducible] homComplexFunctor
set_option backward.isDefEq.respectTransparency true

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{max c v r}}

set_option hygiene false in
local notation "𝓡" =>
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R
set_option hygiene false in
local notation "Mod" => SheafOfModules.{max c v r} 𝓡

private noncomputable def rhomNormalizedHomFactorEquiv (M N : Mod) :
    (SheafOfModules.unit 𝓡 ⟶ SheafOfModules.homObj (R := R) M N) ≃+ (M ⟶ N) where
  toEquiv := (SheafOfModules.unitHomEquiv _).trans
    (SheafOfModules.homObjSectionsEquiv M N)
  map_add' f g := by rfl

attribute [local irreducible] rhomNormalizedHomFactorEquiv

/-- Construct the global-cochain comparison from a specified product cone.
The inverse is the unique lift to that product. -/
private noncomputable def rhomNormalizedHomGlobalCochainsOfFan (A B : CochainComplex Mod ℤ) (n : ℤ)
    (Z : Mod) (π : ∀ p q : ℤ, p + n = q → (Z ⟶
      SheafOfModules.homObj (R := R) (A.X p) (B.X q)))
    (hπ : IsLimit (Fan.mk Z (fun p ↦ π p (p + n) rfl))) :
    (SheafOfModules.unit 𝓡 ⟶ Z) ≃+ CochainComplex.HomComplex.Cochain A B n :=
    { toFun s := CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
        rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X q) (s ≫ π p q hpq)
      invFun c := Fan.IsLimit.lift hπ fun p ↦
        (rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)
      left_inv s := by
        apply Fan.IsLimit.hom_ext hπ
        intro p
        simpa using Fan.IsLimit.fac hπ (fun p ↦
          s ≫ π p (p + n) rfl) p
      right_inv c := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        subst q
        change rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + n))
          (Fan.IsLimit.lift hπ (fun p ↦
            (rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + n))).symm
              (c.v p (p + n) rfl)) ≫
            π p (p + n) rfl) = c.v p (p + n) rfl
        have hf := Fan.IsLimit.fac hπ (fun p ↦
          (rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)) p
        simp only [fan_mk_proj] at hf
        rw [hf]
        exact AddEquiv.apply_symm_apply _ _
      map_add' s t := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        simp [add_comp] }

attribute [local irreducible] rhomNormalizedHomGlobalCochainsOfFan

end CategoryTheory
