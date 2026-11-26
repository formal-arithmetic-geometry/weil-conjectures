/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting
import WeilConjectures.RingTheory.HenselianFactorizationCriterion
import WeilConjectures.RingTheory.MonicFactorizationOfIdempotent

/-!
# Integral algebras over henselian pairs

## Main statements

* `henselianRing_of_isIntegral`: an integral algebra over a henselian pair is
  henselian for the extended ideal.

## Implementation details

The extended ideal lies in the Jacobson radical by integrality. A coprime factorization of a
monic polynomial `f` modulo the extended ideal gives an idempotent of `B[X]/(f)` modulo the
ideal, which lifts since `B[X]/(f)` is integral over `A` (idempotent-lifting characterization,
Tag 09XI); the lifted idempotent lifts the factorization.

## References

* [Stacks, Tag 09XK]
* [Stacks, Tag 09XI]
-/

@[expose] public section

universe u v

/-- If `(A, I)` is a henselian pair and `B` is an integral `A`-algebra, then the
extended ideal pair `(B, IB)`, with `IB = I.map (algebraMap A B)`, is henselian. -/
theorem henselianRing_of_isIntegral
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (B : Type v) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] :
    HenselianRing B (I.map (algebraMap A B)) := by
  classical
  let J := I.map (algebraMap A B)
  have hJ : J ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.jacobson, le_sInf_iff]
    rintro M ⟨-, hM⟩
    let : M.IsMaximal := hM
    have hcom : (M.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    apply Ideal.map_le_iff_le_comap.mpr
    exact HenselianRing.jac.trans (sInf_le ⟨bot_le, hcom⟩)
  apply (henselianRing_iff_factorization_criterion B J).1.mpr
  refine ⟨hJ, ?_⟩
  intro f hf g₀ h₀ hg₀ hh₀ hc hfac
  let C := AdjoinRoot f
  let : Module.Finite B C := hf.finite_adjoinRoot
  let AC : Algebra A C := Algebra.compHom C (algebraMap A B)
  let : SMul A C := AC.toSMul
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.trans B
  have hmap : J.map (algebraMap B C) = I.map (algebraMap A C) := by
    rw [Ideal.map_map]
    rfl
  have H : ∀ e₀ : C ⧸ J.map (algebraMap B C), IsIdempotentElem e₀ →
      ∃ e : C, IsIdempotentElem e ∧
        Ideal.Quotient.mk (J.map (algebraMap B C)) e = e₀ := by
    rw [hmap]
    intro e₀ he₀
    obtain ⟨e, he, -⟩ :=
      Algebra.existsUnique_isIdempotentElem_of_henselianRing A I C e₀ he₀
    exact ⟨e, he⟩
  obtain ⟨a, b, hab⟩ := hc
  let p₀ := b * h₀
  obtain ⟨p, hp⟩ := Polynomial.map_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective p₀
  let I := J.map (algebraMap B (AdjoinRoot f))
  let E := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot J f
  let e₀ := Ideal.Quotient.mk I (AdjoinRoot.mk f p)
  have he₀ : IsIdempotentElem e₀ := by
    apply E.injective
    rw [map_mul]
    change (AdjoinRoot.mk (f.map (Ideal.Quotient.mk J)) (p.map (Ideal.Quotient.mk J))) *
      (AdjoinRoot.mk (f.map (Ideal.Quotient.mk J)) (p.map (Ideal.Quotient.mk J))) =
        AdjoinRoot.mk (f.map (Ideal.Quotient.mk J)) (p.map (Ideal.Quotient.mk J))
    rw [hp, ← map_mul, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
    refine ⟨-(a * b), ?_⟩
    dsimp [p₀]
    rw [hfac]
    linear_combination (b * h₀) * hab
  obtain ⟨e, he, heq⟩ := H e₀ he₀
  have hmaps (q : Polynomial (B ⧸ J)) (hq : q ∣ f.map (Ideal.Quotient.mk J)) :
      AdjoinRoot.map (Ideal.Quotient.mk J) f q hq e = AdjoinRoot.mk q p₀ := by
    let φ := AdjoinRoot.map (Ideal.Quotient.mk J) f q hq
    have hker : I ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change φ (algebraMap B (AdjoinRoot f) r) = 0
      simp only [φ, AdjoinRoot.algebraMap_eq, AdjoinRoot.map_of]
      change AdjoinRoot.of q (Ideal.Quotient.mk J r) = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hr, map_zero]
    have h := congrArg (Ideal.Quotient.lift I φ hker) heq
    change φ e = φ (AdjoinRoot.mk f p) at h
    rw [h]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk f p) = _
    rw [AdjoinRoot.lift_mk]
    rw [← Polynomial.eval₂_map]
    rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq, hp]
  have he₁ : AdjoinRoot.map (Ideal.Quotient.mk J) f g₀
      (hfac.symm ▸ dvd_mul_right g₀ h₀) e = 1 := by
    rw [hmaps]
    have h := congrArg (AdjoinRoot.mk g₀) hab
    simpa [p₀, map_add, map_mul, AdjoinRoot.mk_self] using h
  have he₀' : AdjoinRoot.map (Ideal.Quotient.mk J) f h₀
      (hfac.symm ▸ dvd_mul_left h₀ g₀) e = 0 := by
    rw [hmaps]
    simp [p₀, map_mul, AdjoinRoot.mk_self]
  exact Polynomial.exists_monic_factorization_of_idempotent
    J hJ f hf g₀ h₀ hg₀ hh₀ ⟨a, b, hab⟩ hfac e he he₁ he₀'

