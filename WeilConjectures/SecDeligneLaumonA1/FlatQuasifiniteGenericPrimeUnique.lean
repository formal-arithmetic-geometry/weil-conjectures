/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flat quasi-finite localizations have a unique generic prime

Source: Stacks Project, More on Algebra, Tag 0GS5, lemma-ideal-inverse-nonzero,
case (3) and the reduction to case (7) (blueprint:
lem-dl-a1-flat-quasifinite-generic-prime-unique).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

/-- For a finite-type algebra, the isolated-fibre-point definition of quasi-finiteness at
`q` agrees with Mathlib's `Algebra.QuasiFiniteAt`: both say that the point of the fibre
spectrum over `q ∩ A` given by `q` is open (`PrimeSpectrum.preimageHomeomorphFiber`
and `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`). -/
private theorem isQuasiFiniteAtPrime_iff_quasiFiniteAt
    (A : Type*) (C : Type*) [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.FiniteType A C] (q : PrimeSpectrum C) :
    Algebra.IsQuasiFiniteAtPrime A C q ↔
      Algebra.QuasiFiniteAt A q.asIdeal := by
  unfold Algebra.IsQuasiFiniteAtPrime
  let e := PrimeSpectrum.preimageHomeomorphFiber A C
    (q.comap (algebraMap A C))
  have he : IsOpen ({e ⟨q, rfl⟩} : Set _) ↔
      IsOpen (X := PrimeSpectrum.comap (algebraMap A C) ⁻¹'
        {q.comap (algebraMap A C)}) {⟨q, rfl⟩} := by
    simpa only [Set.image_singleton] using
      (e.isOpen_image (s := {⟨q, rfl⟩}))
  exact he.trans (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber q).symm

/-- Let `A` be a domain and `A → C` a finite-type map that is quasi-finite at every
prime of `C`. For a prime `Q` of `C`, if the localization `B = C_Q` is a domain
and the composite `A → C → B` is flat, then the map `A → B` is injective and the
zero prime of `B` is the unique prime contracting to zero in `A`.

Source: Stacks Project, More on Algebra, Tag 0GS5, lemma-ideal-inverse-nonzero,
case (3) and the proof reducing cases (1)--(6) to case (7)
(blueprint: lem-dl-a1-flat-quasifinite-generic-prime-unique).

Proof: `B` is flat over the domain `A`, hence torsion-free; since `B` is a nonzero
domain, every nonzero `a ∈ A` stays nonzero in `B`, so `A → B` is injective. Let
`K = ker(C → B)`; it is prime because `B` is a domain, and it contracts to zero in
`A` by injectivity. The localization order isomorphism sends a prime `P` of `B` to a
prime `P'` of `C` with `K ≤ P' ≤ Q`; if `P` contracts to zero in `A`, so does `P'`.
Quasi-finiteness at `Q` (the fibre point of `Q` is isolated) gives quasi-finiteness of
`C_Q` over `A`, hence at `P' ≤ Q`; in a quasi-finite fibre there is no proper
specialization over one base prime, so `K = P'`. As `K` corresponds to the zero prime
of `B`, the order isomorphism gives `P = 0`.
-/
theorem flat_quasiFinite_genericPrime_unique
    (A : Type u) (C : Type v) [CommRing A] [IsDomain A] [CommRing C]
    [Algebra A C] [Algebra.FiniteType A C]
    (hquasi : ∀ q : PrimeSpectrum C, Algebra.IsQuasiFiniteAtPrime A C q)
    (Q : Ideal C) [Q.IsPrime]
    [IsDomain (Localization.AtPrime Q)]
    (hflat : RingHom.Flat
      ((algebraMap C (Localization.AtPrime Q)).comp (algebraMap A C))) :
    Function.Injective
        ((algebraMap C (Localization.AtPrime Q)).comp (algebraMap A C)) ∧
      ∀ P : Ideal (Localization.AtPrime Q), P.IsPrime →
        P.comap ((algebraMap C (Localization.AtPrime Q)).comp (algebraMap A C)) =
          (⊥ : Ideal A) →
        P = (⊥ : Ideal (Localization.AtPrime Q)) := by
  let f : A →+* Localization.AtPrime Q :=
    (algebraMap C (Localization.AtPrime Q)).comp (algebraMap A C)
  have hinj : Function.Injective f := by
    let _ : Algebra A (Localization.AtPrime Q) := f.toAlgebra
    let _ : Module A (Localization.AtPrime Q) := Algebra.toModule
    have htf : Module.Flat A (Localization.AtPrime Q) := by
      unfold RingHom.Flat at hflat
      exact hflat
    have _ : Module.Flat A (Localization.AtPrime Q) := htf
    exact Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  refine ⟨hinj, ?_⟩
  intro P hP hP0
  let K : Ideal C := RingHom.ker (algebraMap C (Localization.AtPrime Q))
  have hK : K.IsPrime := by
    exact RingHom.ker_isPrime (algebraMap C (Localization.AtPrime Q))
  have hKunder : K.under A = (⊥ : Ideal A) := by
    change (RingHom.ker (algebraMap C (Localization.AtPrime Q))).comap
      (algebraMap A C) = ⊥
    rw [RingHom.comap_ker (algebraMap C (Localization.AtPrime Q)) (algebraMap A C)]
    exact (RingHom.injective_iff_ker_eq_bot f).mp hinj
  have _ : Algebra.QuasiFiniteAt A Q := by
    let qQ : PrimeSpectrum C := ⟨Q, inferInstance⟩
    exact (isQuasiFiniteAtPrime_iff_quasiFiniteAt A C qQ).mp (hquasi qQ)
  let e := IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime Q) Q
  let P' : Ideal C := (e ⟨P, hP⟩).1
  have hP' : P'.IsPrime := (e ⟨P, hP⟩).2.1
  have hP'Q : P' ≤ Q := (e ⟨P, hP⟩).2.2
  have hKP' : K ≤ P' := by
    intro x hx
    have h0 : algebraMap C (Localization.AtPrime Q) x = 0 := RingHom.mem_ker.mp hx
    have hxP : algebraMap C (Localization.AtPrime Q) x ∈ P := by
      rw [h0]
      exact P.zero_mem
    exact hxP
  have hP'under : P'.under A = (⊥ : Ideal A) := by
    change (P.under C).under A = ⊥
    rw [← Ideal.under_under (B := C)]
    exact hP0
  have _ : Algebra.QuasiFiniteAt A P' :=
    Algebra.QuasiFiniteAt.of_le (R := A) hP'Q
  have hKP'Eq : K = P' := by
    apply Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := A) (S := C) hKP'
    exact hKunder.trans hP'under.symm
  have hbot : (e ⟨(⊥ : Ideal (Localization.AtPrime Q)), Ideal.isPrime_bot⟩).1 = K := by
    change (⊥ : Ideal (Localization.AtPrime Q)).under C = K
    rfl
  have he : e ⟨P, hP⟩ = e ⟨(⊥ : Ideal (Localization.AtPrime Q)), Ideal.isPrime_bot⟩ := by
    apply Subtype.ext
    exact hKP'Eq.symm.trans hbot.symm
  exact congrArg Subtype.val (e.injective he)

end RingHom
