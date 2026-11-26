/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.PopescuLiftOnceCore
import WeilConjectures.RingTheory.NakayamaNilpotent

/-!
# Factoring through a quotient of a smooth algebra over a square-zero base

A map from a finitely presented algebra to `Λ` factors through `B / J` with `B` smooth and
`J` finitely generated and contained in the extended square-zero ideal, provided that
`Λ / IΛ` is a filtered colimit of smooth algebras.

## References

* [Stacks, Tag 07CK]
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

/-- A map from a finitely presented algebra factors through `B / J`, with `B` smooth and
`J` finitely generated and contained in the extended square-zero base ideal, provided the
reduction of the target algebra is a filtered colimit of smooth algebras. -/
theorem exists_smooth_quotient_factorization
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ :
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
        (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ (J : Ideal B), J.FG ∧ J ≤ I.map (algebraMap R B) ∧
        ∃ (ψ : A →ₐ[R] B ⧸ J) (χ : B ⧸ J →ₐ[R] Λ), χ.comp ψ = φ := by
  classical
  obtain ⟨A', _, _, hfp, ι, φ', hφ, B, _, _, hB, ⟨e⟩⟩ :=
    exists_smooth_reduction_factorization R Λ I hΛ A φ
  let IA := I.map (algebraMap R A')
  let IB := I.map (algebraMap R B)
  have hIA : IA ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  let γ : B →ₐ[R] A' ⧸ IA := e.toAlgHom.comp (Ideal.Quotient.mkₐ R IB)
  obtain ⟨θ, hθ⟩ := FormallySmooth.comp_surjective R B IA hIA γ
  have hs : Function.Surjective θ := by
    apply RingTheory.surjective_of_surjective_mod_nilpotent R B A' I θ.toLinearMap
      ⟨2, by decide, hI⟩
    intro y
    let E := Submodule.quotEquivOfEq (I • (⊤ : Submodule R A'))
      (IA.restrictScalars R) (Ideal.smul_top_eq_map I)
    obtain ⟨b, hb⟩ := e.surjective (E y)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨(I • (⊤ : Submodule R B)).mkQ x, E.injective ?_⟩
    change E (Submodule.Quotient.mk (θ x)) = E y
    rw [Submodule.quotEquivOfEq_mk]
    exact (DFunLike.congr_fun hθ x).trans hb
  let J := RingHom.ker θ.toRingHom
  have hJfg : J.FG := FinitePresentation.ker_fG_of_surjective θ hs
  have hJI : J ≤ IB := by
    intro b hb
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    have hz : θ b = 0 := hb
    have he := DFunLike.congr_fun hθ b
    change Ideal.Quotient.mk IA (θ b) = e (Ideal.Quotient.mk IB b) at he
    rw [hz, map_zero] at he
    exact he.symm.trans (map_zero e).symm
  let q : (B ⧸ J) ≃ₐ[R] A' := Ideal.quotientKerAlgEquivOfSurjective hs
  refine ⟨B, inferInstance, inferInstance, hB, J, hJfg, hJI, ?_⟩
  let ψ : A →ₐ[R] B ⧸ J := q.symm.toAlgHom.comp ι
  let χ : B ⧸ J →ₐ[R] Λ := φ'.comp q.toAlgHom
  refine ⟨ψ, χ, ?_⟩
  apply AlgHom.ext
  intro x
  change φ' (q (q.symm (ι x))) = φ x
  rw [q.apply_symm_apply]
  exact DFunLike.congr_fun hφ x

end Algebra
