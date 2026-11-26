/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.RingTheory.RegularSequenceConormal
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Cotangent homology of the fraction field of a complete intersection

For `A = k[X₁, …, Xₙ] ⧸ (f)` with `f` a regular sequence and `A` a domain, the cotangent homology
`H1Cotangent k K` and the differentials `Ω[K/k]` of `K = Frac A` are the kernel and cokernel of a
single linear map `K^(length f) → K^n`.

## Implementation details

The regular sequence gives a basis of `I/I²` (00LN) and the polynomial differentials give a basis
of `A ⊗[P] Ω[P/k]`, so the conormal differential is a map `A^(length f) → A^n` with kernel
`H1Cotangent k A` (00S1) and cokernel `Ω[A/k]`. Localizing at all nonzero elements of `A` is
exact and identifies these with the corresponding objects for the fraction field (00S7).

## References

* [Stacks, Tag 07E1] (proof, the displayed two-term complex)
* [Stacks, Tags 00S1, 00S7, 00LN]
-/

@[expose] public section

universe u v

namespace Algebra

/-- The cotangent homology of the fraction field of a polynomial complete intersection
is computed by one linear map between finite coordinate spaces: there is a `K`-linear map
`δ : K^(length f) → K^n` whose kernel is `H1Cotangent k K` and whose cokernel is `Ω[K/k]`. -/
theorem exists_fractionField_completeIntersection_cotangent_model
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (n : ℕ) (f : List (MvPolynomial (Fin n) k))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) f)
    [IsDomain (MvPolynomial (Fin n) k ⧸ Ideal.ofList f)]
    (e : FractionRing (MvPolynomial (Fin n) k ⧸ Ideal.ofList f) ≃ₐ[k] K) :
    ∃ δ : (Fin f.length → K) →ₗ[K] (Fin n → K),
      Nonempty (H1Cotangent k K ≃ₗ[K] LinearMap.ker δ) ∧
      Nonempty (KaehlerDifferential k K ≃ₗ[K] ((Fin n → K) ⧸ LinearMap.range δ)) := by
  classical
  let P := MvPolynomial (Fin n) k
  let I : Ideal P := Ideal.ofList f
  let A := P ⧸ I
  let α : P →ₐ[k] A := Ideal.Quotient.mkₐ k I
  let G : Generators k A (Fin n) :=
    { Generators.ofAlgHom α (Ideal.Quotient.mkₐ_surjective k I) with
      algebra := inferInstance
      algebraMap_eq := by
        change α.toRingHom = (MvPolynomial.aeval (α ∘ MvPolynomial.X)).toRingHom
        congr 1
        exact MvPolynomial.aeval_unique α }
  have hker : G.ker = I := Ideal.mk_ker
  have hI : Ideal.span (Set.range f.get) = I := by
    apply congrArg Ideal.span
    ext x
    exact List.mem_iff_get.symm
  obtain ⟨_, ⟨b, _⟩, _⟩ := RingTheory.Sequence.regularSequence_conormal_free
    P f.length f.get (by simpa only [List.ofFn_get] using hreg)
  rw [hI] at b
  let ecP :=
    G.toExtension.cotangentEquivCotangentKer.trans (Ideal.Cotangent.equivOfEq _ _ hker)
  let ec : G.toExtension.Cotangent ≃ₗ[A] I.Cotangent :=
    ecP.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I))
  let : Algebra A K := (e.toRingHom.comp (algebraMap A (FractionRing A))).toAlgebra
  have : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change (algebraMap k K) x =
      e ((algebraMap A (FractionRing A)) ((algebraMap k A) x))
    rw [← IsScalarTower.algebraMap_apply k A (FractionRing A)]
    exact (e.commutes x).symm)
  have : IsFractionRing A K := IsFractionRing.of_algEquiv
    (show FractionRing A ≃ₐ[A] K from { e.toRingEquiv with commutes' := fun _ ↦ rfl })
  have : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  have : FormallyEtale A K := FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let d := G.toExtension.cotangentComplex.baseChange K
  let ecK : (TensorProduct A K G.toExtension.Cotangent) ≃ₗ[K] (Fin f.length → K) :=
    (LinearEquiv.baseChange A K _ _ ec).trans (b.baseChange K).equivFun
  let evK : (TensorProduct A K G.toExtension.CotangentSpace) ≃ₗ[K] (Fin n → K) :=
    (G.cotangentSpaceBasis.baseChange K).equivFun
  let δ := evK.toLinearMap.comp (d.comp ecK.symm.toLinearMap)
  refine ⟨δ, ?_, ?_⟩
  · let eh := (tensorH1CotangentOfIsLocalization k K (nonZeroDivisors A)).symm.trans
      (LinearEquiv.baseChange A K _ _ G.equivH1Cotangent.symm)
    let et : (TensorProduct A K G.toExtension.H1Cotangent) ≃ₗ[K] LinearMap.ker d :=
      LinearMap.tensorKerEquiv K K G.toExtension.cotangentComplex
    have hk : (LinearMap.ker d).map ecK.toLinearMap = LinearMap.ker δ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [LinearMap.mem_ker, δ, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply]
        rw [LinearMap.mem_ker.mp hy, map_zero]
      · intro hx
        refine ⟨ecK.symm x, ?_, ecK.apply_symm_apply x⟩
        apply LinearMap.mem_ker.mpr
        apply evK.injective
        simpa only [δ, LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
          map_zero] using hx
    exact ⟨eh.trans (et.trans (ecK.ofSubmodules _ _ hk))⟩
  · let q := G.toExtension.toKaehler.baseChange K
    have hq : Function.Surjective q := LinearMap.lTensor_surjective K
      G.toExtension.toKaehler_surjective
    have hex : Function.Exact d q := lTensor_exact K
      G.toExtension.exact_cotangentComplex_toKaehler G.toExtension.toKaehler_surjective
    let eqΩ := (Submodule.quotEquivOfEq (LinearMap.range d) (LinearMap.ker q)
      hex.linearMap_ker_eq.symm).trans (q.quotKerEquivOfSurjective hq)
    have hr : (LinearMap.range d).map evK.toLinearMap = LinearMap.range δ := by
      dsimp only [δ]
      rw [LinearMap.range_comp, LinearEquiv.range_comp]
    let eqδ := Submodule.Quotient.equiv _ _ evK hr
    exact ⟨(KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A K).symm.trans
      (eqΩ.symm.trans eqδ)⟩

end Algebra
