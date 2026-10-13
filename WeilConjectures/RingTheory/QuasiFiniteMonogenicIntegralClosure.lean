/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Integral closure of a monogenic algebra near a quasi-finite prime

Source: Stacks Project, Algebra, Lemma Tag 00Q8
(blueprint: lem-weil-pbc-quasi-finite-monogenic-integral-closure).
-/

@[expose] public section

universe u

namespace Algebra

/-- Stacks Project, Algebra, Lemma Tag 00Q8:
(blueprint: lem-weil-pbc-quasi-finite-monogenic-integral-closure).
The canonical inclusion of the integral closure becomes an isomorphism after localizing
at an integral element outside a quasi-finite prime of a polynomial quotient.

Proof: transport the open singleton defining `IsQuasiFiniteAtPrime` through
`PrimeSpectrum.preimageHomeomorphFiber` to the topological fibre of the map of spectra.
Mathlib's `QuasiFiniteAt.of_isOpen_singleton_fiber` then supplies `QuasiFiniteAt R q.asIdeal`.
The polynomial quotient is a finite-type algebra, so apply
`ZariskisMainProperty.of_finiteType` (Stacks Tag 00Q9). Its conclusion is definitionally
exactly the required witness and bijectivity of the localized inclusion. -/
theorem quasiFiniteAtPrime_monogenic_integralClosure
    (R : Type u) [CommRing R] (I : Ideal (Polynomial R))
    (q : PrimeSpectrum (Polynomial R ⧸ I))
    (hq : IsQuasiFiniteAtPrime R (Polynomial R ⧸ I) q) :
    ∃ g : integralClosure R (Polynomial R ⧸ I), (g : Polynomial R ⧸ I) ∉ q.asIdeal ∧
      Function.Bijective
        (Localization.awayMap (integralClosure R (Polynomial R ⧸ I)).val.toRingHom g) := by
  let p := q.comap (algebraMap R (Polynomial R ⧸ I))
  let e := PrimeSpectrum.preimageHomeomorphFiber R (Polynomial R ⧸ I) p
  have hopen : IsOpen (X := PrimeSpectrum.comap (algebraMap R (Polynomial R ⧸ I)) ⁻¹'
      {p}) {⟨q, rfl⟩} := by
    rw [← e.isOpen_image, Set.image_singleton]
    exact hq
  have : QuasiFiniteAt R q.asIdeal := QuasiFiniteAt.of_isOpen_singleton_fiber q hopen
  exact ZariskisMainProperty.of_finiteType q.asIdeal

end Algebra
