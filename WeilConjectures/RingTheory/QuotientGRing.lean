/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.RegularBaseChange
import Mathlib.RingTheory.RingHom.Surjective

/-!
# Quotients of G-rings

A quotient of a G-ring by any ideal is a G-ring.

## Implementation details

For a prime `p̄` of `S = R/I` with inverse image `p`, the map `A = R_p → S_p̄` is surjective with
kernel `J = IA`. The completion map of `A` is regular, and its base change along `A → S_p̄`
is the completion map of `S_p̄`, since the completion of `S_p̄` is the quotient of the completion
of `A` by `J`. Flatness and geometric regularity of the fibres transport through this
isomorphism.

## References

* [Stacks, Tag 07PP] (3)
-/

@[expose] public section

universe u

private theorem geometricallyRegular_of_algEquiv
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (h : Algebra.IsGeometricallyRegular k A) :
    Algebra.IsGeometricallyRegular k B := by
  have : IsNoetherianRing A := h.1
  refine ⟨isNoetherianRing_of_ringEquiv A e.toRingEquiv, ?_⟩
  intro k' _ _ _ _
  have := h.2 k'
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : k' ≃ₐ[k'] k') e).toRingEquiv

private theorem regular_of_algEquiv
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T)
    (h : (algebraMap R S).IsRegular) : (algebraMap R T).IsRegular := by
  rw [RingHom.IsRegular, toAlgebra_algebraMap] at h ⊢
  refine ⟨?_, ?_⟩
  · have he : e.toRingHom.comp (algebraMap R S) = algebraMap R T := by
      ext x
      exact e.commutes x
    rw [← he]
    exact h.1.comp (RingHom.Flat.of_bijective e.bijective)
  · intro p _
    exact geometricallyRegular_of_algEquiv
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField) e) (h.2 p)

private theorem regular_completion_of_surjective
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A]
    [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ)
    (hreg : (algebraMap A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)).IsRegular) :
    (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).IsRegular := by
  let m := IsLocalRing.maximalIdeal A
  let n := IsLocalRing.maximalIdeal B
  let Ahat := AdicCompletion m A
  let Bhat := AdicCompletion n B
  let J := RingHom.ker φ
  let Jhat := J.map (algebraMap A Ahat)
  -- Completion of the surjection is the quotient by the extended kernel.
  have hc := AdicCompletion.exists_local_completion_quotient A B φ hφ
  dsimp only at hc
  rw [IsLocalRing.map_maximalIdeal_of_surjective φ hφ] at hc
  obtain ⟨_, θ, _, hcomm, _, _, e, he⟩ := hc
  let : Algebra A B := φ.toAlgebra
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_surjective
    (IsScalarTower.toAlgHom A A B) hφ
  let eAB : (A ⧸ J) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective
      (f := IsScalarTower.toAlgHom A A B) hφ
  -- Tensoring the kernel quotient identifies the base change with that quotient.
  let eTensor : TensorProduct A Ahat B ≃+* (Ahat ⧸ Jhat) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : Ahat ≃ₐ[Ahat] Ahat)
      eAB.symm).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Ahat J).symm.toRingEquiv
  let eTotal : TensorProduct A Ahat B ≃+* Bhat := eTensor.trans e
  -- Check compatibility on lifts under φ, which are all the elements of B.
  have hTotal (b : B) : eTotal (Algebra.TensorProduct.includeRight b) =
      algebraMap B Bhat b := by
    obtain ⟨a, rfl⟩ := hφ b
    change e ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot Ahat J).symm
      (Algebra.TensorProduct.congr (AlgEquiv.refl : Ahat ≃ₐ[Ahat] Ahat)
        eAB.symm (TensorProduct.tmul A (1 : Ahat) (φ a)))) = _
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      map_one]
    have hAB : eAB.symm (φ a) = Ideal.Quotient.mk J a :=
      Ideal.quotientKerAlgEquivOfSurjective_symm_apply
        (f := IsScalarTower.toAlgHom A A B) hφ a
    change e ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot Ahat J).symm
      (TensorProduct.tmul A (1 : Ahat) (eAB.symm (φ a)))) = _
    rw [hAB, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    rw [Algebra.smul_def, mul_one]
    exact (he (algebraMap A Ahat a)).trans (DFunLike.congr_fun hcomm a)
  let : Algebra B (TensorProduct A Ahat B) := Algebra.TensorProduct.rightAlgebra
  let eB : TensorProduct A Ahat B ≃ₐ[B] Bhat :=
    { eTotal with commutes' := hTotal }
  -- The B-algebra equivalence identifies includeRight with the completion map.
  have hbase := RingHom.regular_base_change (R' := B) hreg
  exact regular_of_algEquiv eB hbase

/-- A quotient of a G-ring by any ideal is a G-ring. -/
theorem isGRing_quotient {R : Type u} [CommRing R] (hR : IsGRing R) (I : Ideal R) :
    IsGRing (R ⧸ I) := by
  have : IsNoetherianRing R := hR.1
  refine ⟨inferInstance, ?_⟩
  intro pbar _
  let p := pbar.comap (Ideal.Quotient.mk I)
  have : p.IsPrime := Ideal.comap_isPrime (Ideal.Quotient.mk I) pbar
  let φ := Localization.localRingHom p pbar (Ideal.Quotient.mk I) rfl
  have hφ : Function.Surjective φ :=
    RingHom.surjective_localRingHom_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective pbar
  exact regular_completion_of_surjective φ hφ (hR.2 p)
