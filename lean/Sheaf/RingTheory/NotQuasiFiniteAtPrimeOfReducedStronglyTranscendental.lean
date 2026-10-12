/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Algebraic.StronglyTranscendental
public import Sheaf.RingTheory.QuasiFiniteAtPrime
import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Strong transcendence prevents quasi-finiteness for reduced rings

Source: Stacks Project, Algebra, Lemma 10.123.10 (Tag 00Q2)
(blueprint: lem-weil-pbc-reduced-strongly-transcendental-not-quasi-finite).
-/

@[expose] public section

universe u v

namespace Algebra

/-- (blueprint: lem-weil-pbc-reduced-strongly-transcendental-not-quasi-finite)
Stacks Project, Algebra, Lemma 10.123.10 (Tag 00Q2). For an inclusion of reduced rings,
strong transcendence of `x` and module finiteness over `R[x]` prevent quasi-finiteness
at every prime. `FaithfulSMul R S` expresses injectivity of the structure map;
`Algebra.adjoin R {x}` is `R[x]`. The finite-type instance is derived from finiteness,
using finite generation of the singleton subalgebra and transitivity of finite type.

Proof:
1. Factor `Polynomial.aeval x` through `Algebra.adjoin R {x}`. The first map is
surjective by `Algebra.adjoin_singleton_eq_range_aeval`, hence finite. The inclusion
into `S` is finite by the module-finiteness hypothesis, so their composite is finite.
2. If the map were quasi-finite at `q`, its corresponding fibre prime would be an
open singleton. Transport openness through `PrimeSpectrum.preimageHomeomorphFiber`
and apply `Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber`.
3. Mathlib's `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt` (Tag 00Q2)
applied to the finite evaluation map and `q.asIdeal` contradicts `hx`. -/
theorem not_isQuasiFiniteAtPrime_of_reduced_isStronglyTranscendental
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsReduced R] [IsReduced S] [Algebra R S] [FaithfulSMul R S]
    (x : S) (hx : IsStronglyTranscendental R x)
    [Module.Finite (Algebra.adjoin R ({x} : Set S)) S] :
    ∀ q : PrimeSpectrum S,
      ¬ @IsQuasiFiniteAtPrime R S _ _ _
        (Algebra.FiniteType.trans
          (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x))
          (inferInstance : Algebra.FiniteType (Algebra.adjoin R ({x} : Set S)) S)) q := by
  -- Mathlib supplies the reduced-ring argument; prove both interface bridges here.
  let : Algebra.FiniteType R S :=
    Algebra.FiniteType.trans
      (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x))
      (inferInstance : Algebra.FiniteType (Algebra.adjoin R ({x} : Set S)) S)
  have hfinite : (Polynomial.aeval (R := R) x).toRingHom.Finite := by
    let f : Polynomial R →ₐ[R] Algebra.adjoin R ({x} : Set S) :=
      (Polynomial.aeval x).codRestrict _ fun p ↦ by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨p, rfl⟩
    have hf : Function.Surjective f := by
      intro y
      have hy : (y : S) ∈ (Polynomial.aeval (R := R) x).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]
        exact y.property
      obtain ⟨p, hp⟩ := hy
      exact ⟨p, Subtype.ext hp⟩
    exact (RingHom.finite_algebraMap.mpr
      (inferInstance : Module.Finite (Algebra.adjoin R ({x} : Set S)) S)).comp
        (RingHom.Finite.of_surjective f.toRingHom hf)
  intro q hq
  let e := PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S))
  have hopen : IsOpen
      (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {q.comap (algebraMap R S)})
      {⟨q, rfl⟩} := by
    rw [← e.isOpen_image, Set.image_singleton]
    exact hq
  have : Algebra.QuasiFiniteAt R q.asIdeal :=
    Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber q hopen
  exact Algebra.not_isStronglyTranscendental_of_quasiFiniteAt hfinite q.asIdeal hx

end Algebra
