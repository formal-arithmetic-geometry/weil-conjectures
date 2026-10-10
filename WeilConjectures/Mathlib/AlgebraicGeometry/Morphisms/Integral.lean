/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib

/-!
# Fibres of integral morphisms

## Main statements

- `AlgebraicGeometry.Scheme.Hom.eq_of_specializes_of_apply_eq_of_isIntegralHom`: an integral
  morphism identifies no two distinct points `x ⤳ x'` (incomparability).
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Incomparability for integral morphisms**: an integral morphism identifies no two distinct
points `x ⤳ x'`. Over an affine open `V` of `Y` this is the incomparability of primes in an
integral extension of rings (`Ideal.IsIntegral.comap_lt_comap`). -/
lemma Scheme.Hom.eq_of_specializes_of_apply_eq_of_isIntegralHom (f : X ⟶ Y) [IsIntegralHom f]
    {x x' : X} (h : x ⤳ x') (hx : f x = f x') : x = x' := by
  obtain ⟨V, hV, hx'V, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x') (U := ⊤) trivial
  have hx'U : x' ∈ f ⁻¹ᵁ V := hx'V
  have hxU : x ∈ f ⁻¹ᵁ V := h.mem_open (f ⁻¹ᵁ V).isOpen hx'U
  have : IsAffine V := hV
  have : IsAffine (f ⁻¹ᵁ V) := hV.preimage f
  let g := f ∣_ V
  have : IsIntegralHom g := inferInstanceAs (IsIntegralHom (f ∣_ V))
  let a : (f ⁻¹ᵁ V).toScheme := ⟨x, hxU⟩
  let a' : (f ⁻¹ᵁ V).toScheme := ⟨x', hx'U⟩
  have haa' : a ⤳ a' := (f ⁻¹ᵁ V).isOpenEmbedding.toIsInducing.specializes_iff.mp h
  have hga : g a = g a' := Subtype.ext (by
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
    exact hx)
  -- pass to the rings of the two affine schemes
  let A := Γ(V.toScheme, ⊤)
  let B := Γ((f ⁻¹ᵁ V).toScheme, ⊤)
  let _ : Algebra A B := g.appTop.hom.toAlgebra
  have hint : RingHom.IsIntegral (g.app ⊤).hom :=
    ((@HasAffineProperty.iff_of_isAffine _ _ IsIntegralHom.hasAffineProperty _ _ g _).mp
      ‹_›).2
  have : Algebra.IsIntegral A B := ⟨hint⟩
  let P : PrimeSpectrum B := (f ⁻¹ᵁ V).toScheme.isoSpec.hom a
  let P' : PrimeSpectrum B := (f ⁻¹ᵁ V).toScheme.isoSpec.hom a'
  have hPP' : P ≤ P' := (PrimeSpectrum.le_iff_specializes P P').mpr
    (haa'.map (f ⁻¹ᵁ V).toScheme.isoSpec.hom.continuous)
  have hcomap : (Spec.map g.appTop) P = (Spec.map g.appTop) P' := by
    change ((f ⁻¹ᵁ V).toScheme.isoSpec.hom ≫ Spec.map g.appTop) a =
      ((f ⁻¹ᵁ V).toScheme.isoSpec.hom ≫ Spec.map g.appTop) a'
    rw [Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hga]
  have hPeq : P = P' := by
    by_contra hne
    have hlt : P.asIdeal < P'.asIdeal := lt_of_le_of_ne hPP' fun he ↦ hne (PrimeSpectrum.ext he)
    have := Ideal.IsIntegral.comap_lt_comap (R := A) hlt
    exact this.ne (congrArg PrimeSpectrum.asIdeal hcomap)
  have : a = a' := (f ⁻¹ᵁ V).toScheme.isoSpec.hom.homeomorph.injective hPeq
  exact congrArg Subtype.val this

end AlgebraicGeometry
