/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# The torsion of an injective abelian sheaf has no higher cohomology

Let `F` be an injective abelian sheaf on a site and `r` a nonzero integer. Multiplication by `r`
is an epimorphism on `F`: every map from a free sheaf `ℤ[X]` to `F` is divisible by `r`, since
multiplication by `r` on `ℤ[X]` is a monomorphism and `F` is injective, and the free sheaves
separate. Multiplication by `r` on the constant sheaf `ℤ` is a monomorphism, so the long exact
cohomology sequence of `0 ⟶ F[r] ⟶ F ⟶ F ⟶ 0` shows that `Hⁿ⁺¹(F[r]) = 0`
(`CategoryTheory.Abelian.Ext.subsingleton_of_shortExact_smul`).

This is the first step towards the acyclicity of the underlying abelian sheaf of an injective
sheaf of `ℤ/r`-modules, which is a retract of `F[r]` for an injective abelian sheaf `F`.

## Main statements

- `CategoryTheory.Sheaf.epi_zsmul_id_of_injective`: multiplication by `r ≠ 0` is an epimorphism
  on an injective abelian sheaf.
- `CategoryTheory.Sheaf.mono_zsmul_id_constantSheaf`: it is a monomorphism on the constant
  sheaf `ℤ`.
- `CategoryTheory.Sheaf.subsingleton_H_kernel_zsmul_of_injective`: `Hⁿ⁺¹(F[r]) = 0`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Sheaf

open Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v w}]

/-- Multiplication by a nonzero integer is a monomorphism on the free sheaf `ℤ[X]`. -/
lemma mono_zsmul_id_freeYoneda (X : C) {r : ℤ} (hr : r ≠ 0) :
    Mono (r • 𝟙 (freeYoneda J X (AddCommGrpCat.of.{max v w} (ULift ℤ)))) := by
  have := AddCommGrpCat.mono_zsmul_id_ulift_int.{max v w} hr
  have hP : Mono (r • 𝟙 (Presheaf.freeYoneda X (AddCommGrpCat.of.{max v w} (ULift ℤ)))) := by
    rw [NatTrans.mono_iff_mono_app]
    intro Y
    rw [NatTrans.app_zsmul, NatTrans.id_app]
    change Mono (r • 𝟙 (∐ fun _ : (yoneda.obj X).obj Y ↦ AddCommGrpCat.of.{max v w} (ULift ℤ)))
    rw [zsmul_id_sigma]
    exact AddCommGrpCat.mono_sigmaMap (ι := (yoneda.obj X).obj Y)
      (fun _ ↦ r • 𝟙 (AddCommGrpCat.of.{max v w} (ULift ℤ)))
  have : (presheafToSheaf J AddCommGrpCat.{max v w}).map
      (r • 𝟙 (Presheaf.freeYoneda X (AddCommGrpCat.of.{max v w} (ULift ℤ)))) =
      r • 𝟙 (freeYoneda J X (AddCommGrpCat.of.{max v w} (ULift ℤ))) := by
    rw [Functor.map_zsmul, CategoryTheory.Functor.map_id]; rfl
  rw [← this]
  exact Functor.map_mono _ _

/-- Multiplication by a nonzero integer is an epimorphism on an injective abelian sheaf. -/
lemma epi_zsmul_id_of_injective (F : Sheaf J AddCommGrpCat.{max v w}) [Injective F] {r : ℤ}
    (hr : r ≠ 0) : Epi (r • 𝟙 F) := by
  refine Preadditive.epi_of_cancel_zero _ fun {Z} c hc ↦ ?_
  refine (isSeparating J (S := fun _ : Unit ↦ AddCommGrpCat.of.{max v w} (ULift ℤ))
    (by simpa using! AddCommGrpCat.isSeparator_ulift_int.{max v w})) _ _ ?_
  rintro _ ⟨⟨X, -⟩⟩ a
  have := mono_zsmul_id_freeYoneda.{w} J X hr
  have ha : Injective.factorThru a (r • 𝟙 _) ≫ (r • 𝟙 F) = a := by
    have h := Injective.comp_factorThru a (r • 𝟙 _)
    rwa [Preadditive.zsmul_comp, Category.id_comp, ← Category.comp_id (Injective.factorThru _ _),
      ← Preadditive.comp_zsmul] at h
  rw [← ha, Category.assoc, hc, Limits.comp_zero, Limits.comp_zero]

/-- Multiplication by a nonzero integer is a monomorphism on the constant sheaf `ℤ`. -/
lemma mono_zsmul_id_constantSheaf {r : ℤ} (hr : r ≠ 0) :
    Mono (r • 𝟙 ((constantSheaf J AddCommGrpCat.{max v w}).obj
      (AddCommGrpCat.of.{max v w} (ULift ℤ)))) := by
  have := AddCommGrpCat.mono_zsmul_id_ulift_int.{max v w} hr
  have h : (constantSheaf J AddCommGrpCat.{max v w}).map
      (r • 𝟙 (AddCommGrpCat.of.{max v w} (ULift ℤ))) =
      r • 𝟙 ((constantSheaf J AddCommGrpCat.{max v w}).obj
        (AddCommGrpCat.of.{max v w} (ULift ℤ))) := by
    rw [Functor.map_zsmul, CategoryTheory.Functor.map_id]
  rw [← h]
  have : Mono ((Functor.const Cᵒᵖ).map (r • 𝟙 (AddCommGrpCat.of.{max v w} (ULift ℤ)))) := by
    rw [NatTrans.mono_iff_mono_app]
    intro; simpa using this
  exact Functor.map_mono (presheafToSheaf J _) _

variable [HasExt.{max v w} (Sheaf J AddCommGrpCat.{max v w})]

/-- The `r`-torsion `F[r]` of an injective abelian sheaf `F` has no higher cohomology. -/
theorem subsingleton_H_kernel_zsmul_of_injective (F : Sheaf J AddCommGrpCat.{max v w})
    [Injective F] {r : ℤ} (hr : r ≠ 0) (n : ℕ) :
    Subsingleton (H (kernel (r • 𝟙 F)) (n + 1)) := by
  have := mono_zsmul_id_constantSheaf.{w} J hr
  have := epi_zsmul_id_of_injective.{w} J F hr
  exact Abelian.Ext.subsingleton_of_shortExact_smul r (kernel.condition _)
    { exact := ShortComplex.exact_kernel _ } n

end CategoryTheory.Sheaf
