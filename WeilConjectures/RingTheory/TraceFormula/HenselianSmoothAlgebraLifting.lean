/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import WeilConjectures.AlgebraicGeometry.SmoothSectionEtaleLift
import WeilConjectures.RingTheory.HenselizationStageMap

/-!
# Lifting maps from smooth algebras across henselian pairs

For a henselian pair `(A, I)`, every `R`-algebra map from a smooth `R`-algebra to `A / I` lifts
to `A`.

## Implementation details

Put `B = A ⊗[R] S`, a smooth `A`-algebra with an `A`-algebra map to `A / I`. An étale
neighbourhood `A → A'` lifts this map to `B → A'`, and the henselian property gives a
retraction `A' → A`; the composite `S → B → A' → A` is the required lift. All rings are
placed in one common universe (via `Shrink`) for the single-universe inputs.

## References

* Stacks Project, More on Algebra, Tag 0H74.
-/

@[expose] public section

universe u v w

namespace Algebra.Smooth

/-- Every map from a smooth `R`-algebra to `A/I`, for a henselian pair `(A, I)`,
lifts to an `R`-algebra map to `A`. -/
theorem exists_lift_of_henselianRing
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (A : Type w) [CommRing A] [Algebra R A]
    (I : Ideal A) [HenselianRing A I] (τ : S →ₐ[R] A ⧸ I) :
    ∃ τ' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp τ' = τ := by
  classical
  let B₀ := TensorProduct R A S
  have : Small.{w} B₀ := Algebra.FiniteType.small (R := A) (S := B₀)
  let B := Shrink.{w} B₀
  let e : B ≃ₐ[A] B₀ := Shrink.algEquiv A B₀
  let σ₀ : B₀ →ₐ[A] A ⧸ I := AlgHom.liftEquiv R A S (A ⧸ I) τ
  let σ : B →ₐ[A] A ⧸ I := σ₀.comp e.toAlgHom
  have : Algebra.Smooth A B := Algebra.Smooth.of_equiv e.symm
  have hB : AlgebraicGeometry.Smooth
      (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)).mpr
        (RingHom.smooth_algebraMap.mpr inferInstance)
  obtain ⟨A', hA', α, hα, j, hj⟩ :=
    AlgebraicGeometry.exists_etale_lift_of_smooth A B I σ hB
  let q := Ideal.quotientMap (I.map (algebraMap A A'))
    (algebraMap A A') Ideal.le_comap_map
  have hq : q = α.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (α.commutes a).symm
  obtain ⟨r, hr, _⟩ := RingTheory.existsUnique_henselization_stage_map A I A'
    (algebraMap A A') hA' (by
      change Function.Bijective q
      rw [hq]
      exact hα) A I (RingHom.id A)
    (by simp)
  have hr_apply (a : A) : r (algebraMap A A' a) = a := RingHom.congr_fun hr a
  let rA : A' →ₐ[A] A := { r with commutes' := fun a ↦ RingHom.congr_fun hr a }
  have hI : I.map (algebraMap A A') ≤
      RingHom.ker ((Ideal.Quotient.mk I).comp r) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change Ideal.Quotient.mk I (r (algebraMap A A' a)) = 0
    rw [hr_apply a]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let rbar : A' ⧸ I.map (algebraMap A A') →+* A ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp r) hI
  have hbar (x : A ⧸ I) : rbar (α x) = x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [show α (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap A A')) (algebraMap A A' a) from α.commutes a]
    change Ideal.Quotient.mk I (r (algebraMap A A' a)) = Ideal.Quotient.mk I a
    rw [hr_apply a]
  let t : B →ₐ[A] A := rA.comp j
  have ht : (Ideal.Quotient.mkₐ A I).comp t = σ := by
    ext b
    have hb := congrArg rbar (congrFun hj b)
    exact hb.trans (hbar (σ b))
  let t₀ : B₀ →ₐ[A] A := t.comp e.symm.toAlgHom
  refine ⟨(AlgHom.liftEquiv R A S A).symm t₀, ?_⟩
  ext s
  have h := AlgHom.congr_fun ht (e.symm (TensorProduct.tmul R (1 : A) s))
  have hσ₀ : σ₀ (TensorProduct.tmul R (1 : A) s) = τ s := by
    change (1 : A) • τ s = τ s
    exact one_smul A (τ s)
  simpa [t₀, σ, hσ₀] using h

end Algebra.Smooth
