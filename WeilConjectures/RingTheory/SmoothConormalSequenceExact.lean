/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic

/-!
# Exactness of the conormal sequence for a smooth ring map

For a smooth ring map `A → B` and a surjection `A → C` factoring through `B`, the conormal
sequence `0 → I/I² → J/J² → C ⊗[B] Ω[B⁄A] → 0` is exact.

## References

* [Stacks, Tag 06A9]
* [Stacks, Tag 065V]
-/

@[expose] public section

universe u v w

namespace Algebra.Extension

/-- For a smooth ring map `A → B` and a surjection `A → C` factoring through `B`, with
`I = ker (A → C)` and `J = ker (B → C)`, the conormal sequence
`0 → I/I² → J/J² → C ⊗[B] Ω[B⁄A] → 0` is exact. The first map is induced by `A → B`, and
the second is `cotangentComplex`, sending the class of `b ∈ J` to `1 ⊗ db`. -/
theorem smooth_conormal_sequence_exact
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.Smooth A B] (hπ : Function.Surjective (algebraMap A C)) :
    ∃ hβ : Function.Surjective (IsScalarTower.toAlgHom A B C),
      ∃ u : (ofSurjective (Algebra.ofId A C) hπ).Cotangent →ₗ[C]
          (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).Cotangent,
        (∀ (a : (ofSurjective (Algebra.ofId A C) hπ).ker)
          (b : (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).ker),
          (b.1 : B) = algebraMap A B (a.1 : A) →
            u (Cotangent.mk a) = Cotangent.mk b) ∧
        Function.Injective u ∧
        Function.Exact u
          (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).cotangentComplex ∧
        Function.Surjective
          (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).cotangentComplex := by
  classical
  have hβ : Function.Surjective (IsScalarTower.toAlgHom A B C) := by
    intro c
    obtain ⟨a, rfl⟩ := hπ c
    exact ⟨algebraMap A B a, (IsScalarTower.algebraMap_apply A B C a).symm⟩
  let P := ofSurjective (Algebra.ofId A C) hπ
  let Q := ofSurjective (IsScalarTower.toAlgHom A B C) hβ
  let i : P.Hom Q :=
    { toRingHom := algebraMap A B
      toRingHom_algebraMap := by intro a; rfl
      algebraMap_toRingHom := by
        intro a
        exact (IsScalarTower.algebraMap_apply A B C a).symm }
  have : Algebra.FormallySmooth A Q.Ring :=
    inferInstanceAs (Algebra.FormallySmooth A B)
  -- Lift the smooth algebra into A/I², as in Stacks 06A7.
  let σ : Q.Ring →ₐ[A] P.infinitesimal.Ring :=
    Algebra.FormallySmooth.liftOfSurjective (IsScalarTower.toAlgHom A Q.Ring C)
      (IsScalarTower.toAlgHom A P.infinitesimal.Ring C)
      P.infinitesimal.algebraMap_surjective
      ⟨2, by
        change P.infinitesimal.ker ^ 2 = ⊥
        rw [ker_infinitesimal]
        exact Ideal.cotangentIdeal_square _⟩
  let r : Q.Hom P.infinitesimal :=
    { toRingHom := σ.toRingHom
      toRingHom_algebraMap := by intro a; exact σ.commutes a
      algebraMap_toRingHom := by
        intro b
        simpa only [σ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          IsScalarTower.toAlgHom_apply, algebraMap_self, RingHom.id_apply] using
          Algebra.FormallySmooth.liftOfSurjective_apply (IsScalarTower.toAlgHom A Q.Ring C)
            (IsScalarTower.toAlgHom A P.infinitesimal.Ring C)
            P.infinitesimal.algebraMap_surjective
            ⟨2, by
              change P.infinitesimal.ker ^ 2 = ⊥
              rw [ker_infinitesimal]
              exact Ideal.cotangentIdeal_square _⟩ b }
  -- The induced conormal map is a left inverse after the infinitesimal identification.
  have hri : r.comp i = P.toInfinitesimal := by
    ext a
    exact σ.commutes a
  have hi : P.ker ≤ Q.ker.comap i.toRingHom := by
    intro a ha
    change algebraMap Q.Ring C (i.toRingHom a) = 0
    rw [i.algebraMap_toRingHom]
    simpa using ha
  let i' : P.infinitesimal.Hom Q.infinitesimal :=
    { toRingHom := Ideal.quotientMap (Q.ker ^ 2) i.toRingHom
        ((Ideal.pow_right_mono hi 2).trans (Ideal.le_comap_pow _ _))
      toRingHom_algebraMap := by
        intro a
        change Ideal.Quotient.mk _ (i.toRingHom (algebraMap A P.Ring a)) = _
        rw [i.toRingHom_algebraMap]
        rfl
      algebraMap_toRingHom := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact i.algebraMap_toRingHom a }
  have hit : i'.comp P.toInfinitesimal = Q.toInfinitesimal.comp i := by
    ext a
    rfl
  let u := Cotangent.map i
  refine ⟨hβ, u, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rw [Cotangent.map_mk]
    congr 1
    exact Subtype.ext hab.symm
  · intro x y hxy
    apply (Cotangent.map_toInfinitesimal_bijective P).injective
    have he := congrArg (Cotangent.map r) hxy
    change ((Cotangent.map r) ∘ₗ Cotangent.map i) x =
      ((Cotangent.map r) ∘ₗ Cotangent.map i) y at he
    have hm := Cotangent.map_comp P.infinitesimal i r
    change Cotangent.map (r.comp i) = Cotangent.map r ∘ₗ Cotangent.map i at hm
    rw [hri] at hm
    rw [hm]
    exact he
  · apply LinearMap.exact_of_comp_of_mem_range
    · ext x
      obtain ⟨a, rfl⟩ := Cotangent.mk_surjective x
      change Q.cotangentComplex (Cotangent.map i (Cotangent.mk a)) = 0
      rw [Cotangent.map_mk, cotangentComplex_mk]
      change TensorProduct.tmul Q.Ring (1 : C)
        (KaehlerDifferential.D A Q.Ring (algebraMap A Q.Ring a.1)) = 0
      simp
    · intro x hx
      let f := Q.toInfinitesimal
      let g := i'.comp r
      -- The difference of these extension maps factors through the differential.
      have hd := DFunLike.congr_fun (Cotangent.map_sub_map f g) x
      change Cotangent.map f x - Cotangent.map g x = f.sub g (Q.cotangentComplex x) at hd
      rw [hx, map_zero, sub_eq_zero] at hd
      obtain ⟨y, hy⟩ := (Cotangent.map_toInfinitesimal_bijective P).surjective
        (Cotangent.map r x)
      refine ⟨y, ?_⟩
      apply (Cotangent.map_toInfinitesimal_bijective Q).injective
      have hm₁ := Cotangent.map_comp Q.infinitesimal i Q.toInfinitesimal
      have hm₂ := Cotangent.map_comp Q.infinitesimal P.toInfinitesimal i'
      have hm₃ := Cotangent.map_comp Q.infinitesimal r i'
      change Cotangent.map (Q.toInfinitesimal.comp i) =
        Cotangent.map Q.toInfinitesimal ∘ₗ Cotangent.map i at hm₁
      change Cotangent.map (i'.comp P.toInfinitesimal) =
        Cotangent.map i' ∘ₗ Cotangent.map P.toInfinitesimal at hm₂
      change Cotangent.map g = Cotangent.map i' ∘ₗ Cotangent.map r at hm₃
      change Cotangent.map Q.toInfinitesimal (Cotangent.map i y) = Cotangent.map f x
      rw [← LinearMap.comp_apply, ← hm₁, ← hit, hm₂, LinearMap.comp_apply, hy]
      rw [← LinearMap.comp_apply, ← hm₃]
      exact hd.symm
  · have : Subsingleton (KaehlerDifferential A C) :=
      KaehlerDifferential.subsingleton_of_surjective A C hπ
    intro x
    exact Q.exact_cotangentComplex_toKaehler x |>.mp (Subsingleton.elim _ _)

end Algebra.Extension
