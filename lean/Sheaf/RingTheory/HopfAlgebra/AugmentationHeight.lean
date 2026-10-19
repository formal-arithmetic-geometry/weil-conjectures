/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import Sheaf.RingTheory.IntegralExtensionDimension
import WeilConjectures.RingTheory.KrullDimension.GoingDown

/-!
# The augmentation ideal has the dimension of a finite type group

Source: blueprint `lem-wf-same-lie-closed-subgroup`, proof, Dimension paragraph:
translations identify all closed-point local dimensions, and their maximum is the
global dimension. This argument is independent of smoothness and characteristic.
(blueprint: lem-wf-hopf-augmentation-height).
-/

@[expose] public section

namespace HopfAlgebra

open Bialgebra WithConv
open scoped TensorProduct

variable {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]

/-- The translation `a ↦ ∑ h(a₁) a₂` of a commutative Hopf algebra by a `k`-point `h`. -/
private noncomputable def heightTranslation (h : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (toConv ((Algebra.ofId k A).comp h.ofConv) * toConv (AlgHom.id k A)).ofConv

private theorem comp_ofId_comp (f : A →ₐ[k] A) (h : A →ₐ[k] k) :
    f.comp ((Algebra.ofId k A).comp h) = (Algebra.ofId k A).comp h := by
  rw [← AlgHom.comp_assoc, Subsingleton.elim (f.comp (Algebra.ofId k A)) (Algebra.ofId k A)]

private theorem heightTranslation_comp_heightTranslation (h₁ h₂ : WithConv (A →ₐ[k] k)) :
    (heightTranslation h₁).comp (heightTranslation h₂) = heightTranslation (h₂ * h₁) := by
  rw [heightTranslation, heightTranslation, AlgHom.comp_convMul_distrib, comp_ofId_comp,
    AlgHom.comp_id, heightTranslation, AlgHom.comp_convMul_distrib (Algebra.ofId k A)]
  simp only [toConv_ofConv, mul_assoc]

private theorem heightTranslation_one :
    heightTranslation (1 : WithConv (A →ₐ[k] k)) = AlgHom.id k A := by
  rw [heightTranslation, AlgHom.convOne_def, ofConv_toConv, ← AlgHom.comp_assoc,
    Subsingleton.elim ((Algebra.ofId k A).comp (Algebra.ofId k k))
      (Algebra.ofId k A),
    ← AlgHom.convOne_def, toConv_ofConv, one_mul, ofConv_toConv]

private theorem comp_heightTranslation_inv (g : WithConv (A →ₐ[k] k)) :
    g.ofConv.comp (heightTranslation g⁻¹) = counitAlgHom k A := by
  rw [heightTranslation, AlgHom.comp_convMul_distrib, ← AlgHom.comp_assoc,
    Subsingleton.elim (g.ofConv.comp (Algebra.ofId k A)) (AlgHom.id k k), AlgHom.id_comp,
    AlgHom.comp_id, toConv_ofConv, toConv_ofConv, inv_mul_cancel, AlgHom.convOne_def,
    ofConv_toConv, Subsingleton.elim (Algebra.ofId k k) (AlgHom.id k k), AlgHom.id_comp]

private theorem exists_heightTranslation (g : A →ₐ[k] k) :
    ∃ τ : A ≃ₐ[k] A, g.comp τ.toAlgHom = counitAlgHom k A := by
  have h₁ : (heightTranslation (toConv g)⁻¹).comp (heightTranslation (toConv g)) =
      AlgHom.id k A := by
    rw [heightTranslation_comp_heightTranslation, mul_inv_cancel, heightTranslation_one]
  have h₂ : (heightTranslation (toConv g)).comp (heightTranslation (toConv g)⁻¹) =
      AlgHom.id k A := by
    rw [heightTranslation_comp_heightTranslation, inv_mul_cancel, heightTranslation_one]
  refine ⟨AlgEquiv.ofAlgHom _ _ h₁ h₂, ?_⟩
  have h := comp_heightTranslation_inv (toConv g)
  rwa [ofConv_toConv] at h

private theorem height_ker_counit_eq_of_isAlgClosed
    [IsAlgClosed k] [Algebra.FiniteType k A] :
    ((RingHom.ker (counitAlgHom k A)).height : WithBot ℕ∞) = ringKrullDim A := by
  apply le_antisymm
  · exact Ideal.height_le_ringKrullDim_of_ne_top (RingHom.ker_ne_top _)
  · apply (ringKrullDim_le_iff_isMaximal_height_le _).mpr
    intro m hm
    let := hm
    obtain ⟨g, rfl⟩ := exists_algHom_ker_eq_of_isMaximal k A m
    obtain ⟨τ, hτ⟩ := exists_heightTranslation g
    have heq : (RingHom.ker g).comap τ.toRingEquiv.toRingHom =
        RingHom.ker (counitAlgHom k A) := by
      ext a
      change g (τ a) = 0 ↔ counitAlgHom k A a = 0
      rw [← hτ]
      rfl
    rw [← heq]
    exact le_of_eq (congrArg (fun h : ℕ∞ ↦ (h : WithBot ℕ∞))
      (τ.toRingEquiv.height_comap (RingHom.ker g))).symm

private theorem height_under_eq_of_integral_of_goingDown
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : (P.under R).height = P.height := by
  let f := PrimeSpectrum.comap (algebraMap R S)
  have hf : StrictMono f := fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap h
  have hlift : ∀ a : PrimeSpectrum S, ∀ b : PrimeSpectrum R,
      b < f a → ∃ a' : PrimeSpectrum S, a' < a ∧ f a' = b := by
    intro a b h
    obtain ⟨Q, hQ, hprime, hlies⟩ :=
      a.asIdeal.exists_ideal_lt_liesOver_of_lt (p := b.asIdeal)
        (q := a.asIdeal.under R) h
    refine ⟨⟨Q, hprime⟩, hQ, ?_⟩
    exact PrimeSpectrum.ext hlies.over.symm
  have h := Order.height_eq_of_strictMono f hf hlift (⟨P, inferInstance⟩ : PrimeSpectrum S)
  rw [← PrimeSpectrum.height_eq_orderHeight,
    ← PrimeSpectrum.height_eq_orderHeight] at h
  exact h.symm

/-- The local dimension at the identity of a finite type affine group scheme equals
its global dimension, even for a nonreduced group scheme in positive characteristic.

Source: `lem-wf-same-lie-closed-subgroup`, proof, Dimension paragraph (the translation
and maximum argument), extended to arbitrary fields by algebraic closure.

Proof in words: first suppose `k` is algebraically closed. Every maximal ideal is the
kernel of a `k`-point, by the weak Nullstellensatz for finite type algebras. For a point
`g`, convolution with `g` defines a translation automorphism; convolution with its
inverse is the inverse automorphism, and the counit identities show that it carries
the identity point to `g`. The induced local ring isomorphism shows that the height
of `ker g` is the height of the augmentation ideal. The Krull dimension of a
nontrivial ring is the supremum of the heights of its maximal ideals. Consequently
it equals this common height. Nontriviality follows from the counit onto the field.

For general `k`, let `K` be its algebraic closure and put `B = K ⊗[k] A`, with its
base-changed Hopf structure. The map `A → B` is faithfully flat and integral: `K/k`
is algebraic, so every finite subset of `B` is contained in the base change by a
finite extension. Thus going-up, incomparability and lying-over identify the global
Krull dimensions of `A` and `B`. The augmentation ideal of `B` contracts to that of
`A`, and its fibre is `K ⊗[k] (A/ker ε) = K`. The local flat dimension formula for
Noetherian local rings therefore gives equal local dimensions at these two
augmentation ideals (the fibre is a field of dimension zero). These local dimensions
are their heights. Apply the algebraically closed case to `B` and substitute both
equalities. No reducedness, regularity or characteristic assumption is used.
(blueprint: lem-wf-hopf-augmentation-height). -/
theorem height_ker_counit_eq_ringKrullDim
    (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] :
    ((RingHom.ker (Bialgebra.counitAlgHom k A)).height : WithBot ℕ∞) =
      ringKrullDim A := by
  let K := AlgebraicClosure k
  let B := K ⊗[k] A
  let C := A ⊗[k] K
  let e : C ≃ₐ[k] B := Algebra.TensorProduct.comm k A K
  have : Algebra.FiniteType K B := by infer_instance
  have : Algebra.IsIntegral A C := inferInstance
  have : Module.FaithfullyFlat A C := inferInstance
  have hdimC : ringKrullDim C = ringKrullDim A := by
    apply le_antisymm
    · exact (RingHom.integralExtensionDimension (algebraMap A C)
        (Algebra.IsIntegral.isIntegral (R := A))).1
    · exact ringKrullDim_le_of_goingDown_of_surjective (algebraMap A C)
        (by
          change @Algebra.HasGoingDown A C _ _ (algebraMap A C).toAlgebra
          rw [toAlgebra_algebraMap]
          infer_instance)
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
  have : (RingHom.ker (counitAlgHom K B)).IsPrime := RingHom.ker_isPrime _
  let P : Ideal C := (RingHom.ker (counitAlgHom K B)).comap e.toRingEquiv.toRingHom
  have : P.IsPrime := inferInstance
  have hcontract : P.under A = RingHom.ker (counitAlgHom k A) := by
    ext a
    change counitAlgHom K B (e (algebraMap A C a)) = 0 ↔ counitAlgHom k A a = 0
    simp [e, C, B, Algebra.TensorProduct.algebraMap_apply,
      Bialgebra.TensorProduct.counitAlgHom_def]
  have hheight : (RingHom.ker (counitAlgHom k A)).height =
      (RingHom.ker (counitAlgHom K B)).height := by
    rw [← hcontract, height_under_eq_of_integral_of_goingDown P]
    exact e.toRingEquiv.height_comap _
  calc
    ((RingHom.ker (counitAlgHom k A)).height : WithBot ℕ∞) =
        (RingHom.ker (counitAlgHom K B)).height := congrArg WithBot.some hheight
    _ = ringKrullDim B := height_ker_counit_eq_of_isAlgClosed
    _ = ringKrullDim C := (RingEquiv.ringKrullDim e.toRingEquiv).symm
    _ = ringKrullDim A := hdimC

end HopfAlgebra
