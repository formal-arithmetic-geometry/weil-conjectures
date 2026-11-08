/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Submission.WeilConjectures.RingTheory.CompleteIntersectionOverField
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Submission.WeilConjectures.RingTheory.FibreLocalRingNaturalIso

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Comparison of a fixed polynomial presentation with its closed fibre

Source: Stacks Project, Tag 00SY, proof of (3) implies (2), first two paragraphs;
Tag 0H9M for the localized fibre comparison.
(blueprint: lem-weil-pbc-syntomic-polynomial-fibre-comparison).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def polynomial_fiber_equiv_quotient
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S) (hφ : Function.Surjective φ)
    (p : Ideal R) [p.IsPrime] :
    p.Fiber S ≃ₐ[p.ResidueField] MvPolynomial (Fin n) p.ResidueField ⧸
      ((RingHom.ker φ.toRingHom).map (MvPolynomial.map (algebraMap R p.ResidueField))) := by
  let k := p.ResidueField
  let Ibar := (RingHom.ker φ.toRingHom).map (MvPolynomial.map (algebraMap R k))
  let D := MvPolynomial (Fin n) k ⧸ Ibar
  refine .ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId k D)
    (AlgHom.liftOfSurjective φ hφ
      ((Ideal.Quotient.mkₐ R Ibar).comp (MvPolynomial.mapAlgHom (Algebra.ofId R k))) ?_)
    (fun _ _ ↦ .all _ _))
    (Ideal.Quotient.liftₐ Ibar
      (MvPolynomial.aeval (fun i ↦ (1 ⊗ₜ[R] φ (MvPolynomial.X i) : p.Fiber S))) ?_) ?_ ?_
  · simp [Ibar, AlgHom.comp_toRingHom, ← RingHom.comap_ker,
      ← Ideal.map_le_iff_le_comap]
  · change Ibar ≤ RingHom.ker (MvPolynomial.aeval _).toRingHom
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
    have hh : ((MvPolynomial.aeval
        (fun i ↦ (1 ⊗ₜ[R] φ (MvPolynomial.X i) : p.Fiber S))).restrictScalars R).comp
        (MvPolynomial.mapAlgHom (Algebra.ofId R k)) =
        Algebra.TensorProduct.includeRight.comp φ := by
      ext i
      simp
    exact .trans_eq (by intro; aesop) congr(RingHom.ker $hh).symm
  · apply Ideal.Quotient.algHom_ext
    ext i
    simp [Ibar, k, Ideal.Quotient.liftₐ]
  · ext x
    obtain ⟨x, rfl⟩ := hφ x
    have hh : ((MvPolynomial.aeval
        (fun i ↦ (1 ⊗ₜ[R] φ (MvPolynomial.X i) : p.Fiber S))).restrictScalars R).comp
        (MvPolynomial.mapAlgHom (Algebra.ofId R k)) =
        Algebra.TensorProduct.includeRight.comp φ := by
      ext i
      simp
    simp only [AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
      AlgHom.id_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
      AlgHom.liftOfSurjective_apply, AlgHom.comp_apply]
    exact AlgHom.congr_fun hh x


private theorem polynomial_fiber_equiv_quotient_tmul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S) (hφ : Function.Surjective φ)
    (p : Ideal R) [p.IsPrime] (a : p.ResidueField) (b : MvPolynomial (Fin n) R) :
    polynomial_fiber_equiv_quotient n φ hφ p (a ⊗ₜ[R] φ b) =
      Ideal.Quotient.mk _
        (MvPolynomial.C a * MvPolynomial.map (algebraMap R p.ResidueField) b) := by
  simp only [polynomial_fiber_equiv_quotient, AlgEquiv.ofAlgHom_apply,
    Algebra.TensorProduct.lift_tmul, AlgHom.liftOfSurjective_apply,
    AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply]
  change algebraMap p.ResidueField _ a * Ideal.Quotient.mk _ _ = _
  rw [← Ideal.Quotient.mk_algebraMap, ← map_mul]
  rfl

private theorem completeIntersection_of_algEquiv
    {k T U : Type*} [Field k] [CommRing T] [CommRing U] [Algebra k T] [Algebra k U]
    (e : T ≃ₐ[k] U) (h : IsGlobalCompleteIntersection k U) :
    IsGlobalCompleteIntersection k T := by
  rcases h with hzero | ⟨n, c, f, hcn, ⟨E⟩, hdim⟩
  · exact Or.inl (e.toEquiv.subsingleton_congr.mpr hzero)
  · refine Or.inr ⟨n, c, f, hcn, ⟨E.trans e.symm⟩, ?_⟩
    let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
    exact H.isHomeomorph.topologicalKrullDim_eq.trans hdim

end Algebra
