/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Vanishing of `Ext` into torsion subobjects of injective objects

Let `J` be an injective object of an abelian category and `r` an integer such that
multiplication by `r` is an epimorphism on `J`, with kernel `ι : K ⟶ J`. If `U` is an object on
which multiplication by `r` is a monomorphism, then `Ext U K (n + 1) = 0` for all `n`: in the
long exact sequence of `0 ⟶ K ⟶ J ⟶ J ⟶ 0`, the groups `Ext U J (n + 1)` vanish, and
multiplication by `r` on `Hom(U, J)` is onto since `J` is injective. The same then holds for any
retract of `K`.

For abelian sheaves, with `U` the constant sheaf `ℤ` and `J` an injective sheaf, this shows that
the `r`-torsion `J[r]` of an injective sheaf, and hence any sheaf of `ℤ/r`-modules which is
injective as such, has no higher cohomology.

## Main statements

- `CategoryTheory.Abelian.Ext.subsingleton_of_shortExact_smul`: the vanishing for `K`.
- `CategoryTheory.Abelian.Ext.subsingleton_of_retract`: `Ext` into a retract.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Let `0 ⟶ K ⟶ J ⟶ J ⟶ 0` be short exact with second map multiplication by `r` and `J`
injective, and let `r` act injectively on `U`. Then `Ext U K (n + 1) = 0`. -/
theorem subsingleton_of_shortExact_smul {U K J : C} [Injective J] (r : ℤ) [Mono (r • 𝟙 U)]
    {ι : K ⟶ J} (w : ι ≫ (r • 𝟙 J : J ⟶ J) = 0) (hS : (ShortComplex.mk ι (r • 𝟙 J) w).ShortExact)
    (n : ℕ) : Subsingleton (Ext.{w} U K (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hx : x.comp (mk₀ ι) (add_zero _) = 0 := eq_zero_of_injective _
  obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ U hS x hx rfl
  rcases n with _ | n
  · -- `y : Hom(U, J)` is divisible by `r`, since `J` is injective
    obtain ⟨g, rfl⟩ := (mk₀_bijective U J).2 y
    let h : U ⟶ J := Injective.factorThru g (r • 𝟙 U)
    have hh : h ≫ (r • 𝟙 J) = g := by
      rw [Preadditive.comp_zsmul, Category.comp_id, ← Category.id_comp h,
        ← Preadditive.zsmul_comp]
      exact Injective.comp_factorThru g (r • 𝟙 U)
    rw [← hh, ← mk₀_comp_mk₀, comp_assoc_of_second_deg_zero, hS.comp_extClass, comp_zero]
  · rw [eq_zero_of_injective y, zero_comp]

/-- `Ext` into a retract of an object with vanishing `Ext` vanishes. -/
theorem subsingleton_of_retract {U F K : C} (i : F ⟶ K) (p : K ⟶ F) (hip : i ≫ p = 𝟙 F)
    (n : ℕ) [Subsingleton (Ext.{w} U K n)] : Subsingleton (Ext.{w} U F n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have : x = (x.comp (mk₀ i) (add_zero n)).comp (mk₀ p) (add_zero n) := by
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, hip, comp_mk₀_id]
  rw [this, Subsingleton.elim (x.comp (mk₀ i) (add_zero n)) 0, zero_comp]

end CategoryTheory.Abelian.Ext
