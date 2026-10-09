/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# The absolute Frobenius of a scheme of characteristic `p`

Let `X` be a scheme on which a prime `p` vanishes. The `n`-th power of the absolute Frobenius
`F^n : X ⟶ X` is the identity on the underlying space and `a ↦ a ^ p ^ n` on the structure
sheaf. It is affine and surjective, being the identity on points.

If `X` is moreover quasi-compact and locally noetherian, the nilpotency index of the nilpotent
sections of `X` is bounded, so a power of the Frobenius kills the nilradical of `X` and factors
through the reduced closed subscheme `X_red`. This gives a surjective affine morphism
`X ⟶ X_red`, which is used to pull back ample families from `X_red` to `X`.

## Main definitions

- `AlgebraicGeometry.Scheme.frobeniusPow`: the `n`-th power of the absolute Frobenius.

## Main statements

- `AlgebraicGeometry.Scheme.exists_surjective_isAffineHom_nilradical_subscheme`: a quasi-compact
  locally noetherian scheme of characteristic `p` admits a surjective affine morphism to its
  reduction.

## Implementation notes

The predicate `AlgebraicGeometry.Scheme.Hom.IsFrobenius` of
`WeilConjectures/AlgebraicGeometry/Frobenius.lean` characterises the Frobenius on affine probes;
here the endomorphism is constructed directly as a morphism of locally ringed spaces.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- If a prime `p` vanishes on `X`, it vanishes on every ring of sections of `X`. -/
lemma natCast_eq_zero_of_natCast_eq_zero_top {X : Scheme.{u}} {p : ℕ} (h : (p : Γ(X, ⊤)) = 0)
    (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  rw [← map_natCast (X.presheaf.map (homOfLE le_top).op).hom, h, map_zero]

section frobeniusPow

variable (X : Scheme.{u}) {p : ℕ} (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (n : ℕ)

/-- The `n`-th power of the **absolute Frobenius** of a scheme `X` on which a prime `p` vanishes:
the identity on the underlying space and `a ↦ a ^ p ^ n` on the structure sheaf. -/
noncomputable def frobeniusPow : X ⟶ X where
  base := 𝟙 _
  c :=
  { app U := CommRingCat.ofHom (powPrimePowRingHom Γ(X, U.unop) hp
      (natCast_eq_zero_of_natCast_eq_zero_top h U.unop) n)
    naturality U V i := by
      ext a
      exact (map_pow (X.presheaf.map i).hom a _).symm }
  prop x := by
    refine ⟨fun a ha ↦ ?_⟩
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
    rw [PresheafedSpace.stalkMap_germ_apply] at ha
    refine (isUnit_pow_iff (pow_ne_zero n hp.ne_zero)).mp ?_
    rw [← map_pow]
    exact ha

lemma frobeniusPow_apply (x : X) : X.frobeniusPow hp h n x = x := rfl

lemma frobeniusPow_app (U : X.Opens) (a : Γ(X, U)) :
    (X.frobeniusPow hp h n).app U a = a ^ p ^ n := rfl

instance : IsAffineHom (X.frobeniusPow hp h n) := ⟨fun _ hU ↦ hU⟩

instance : Surjective (X.frobeniusPow hp h n) := ⟨fun x ↦ ⟨x, rfl⟩⟩

end frobeniusPow

/-- A quasi-compact locally noetherian scheme `X` on which a prime `p` vanishes admits a
surjective affine morphism to its reduction `X_red`: a power of the absolute Frobenius kills the
nilradical of `X`, hence factors through `X_red`. -/
theorem exists_surjective_isAffineHom_nilradical_subscheme (X : Scheme.{u}) [CompactSpace X]
    [IsLocallyNoetherian X] {p : ℕ} (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) :
    ∃ f : X ⟶ X.nilradical.subscheme, Surjective f ∧ IsAffineHom f := by
  obtain ⟨N, hN⟩ := exists_pow_eq_zero_of_isNilpotent X
  have hle : X.nilradical ≤ (X.frobeniusPow hp h N).ker :=
    IdealSheafData.le_ofIdeals_iff.mpr fun U a ha ↦ by
      obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp ha
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self hp.one_lt).le
      rw [RingHom.mem_ker, frobeniusPow_app, hk, pow_add, hN U a ⟨m, Ideal.mem_bot.mp hm⟩]
      exact zero_mul _
  have hι : ((X.frobeniusPow hp h N).toImage ≫ IdealSheafData.inclusion hle) ≫
      X.nilradical.subschemeι = X.frobeniusPow hp h N := by
    rw [Category.assoc, IdealSheafData.inclusion_subschemeι, Hom.toImage_imageι]
  refine ⟨(X.frobeniusPow hp h N).toImage ≫ IdealSheafData.inclusion hle,
    ⟨fun y ↦ ⟨X.nilradical.subschemeι y,
      X.nilradical.subschemeι.isClosedEmbedding.injective ?_⟩⟩, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hι]
    rfl
  · have : IsAffineHom (((X.frobeniusPow hp h N).toImage ≫ IdealSheafData.inclusion hle) ≫
        X.nilradical.subschemeι) := by
      rw [hι]
      infer_instance
    exact .of_comp _ X.nilradical.subschemeι

end AlgebraicGeometry.Scheme
