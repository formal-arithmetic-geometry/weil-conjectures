/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.ProEtale.WeakDimension

/-! # A weakly etale algebra does not increase Krull dimension

Source: Greco, Two theorems on excellent rings (1976), Lemma 5.5, the local AF
comparison; Stacks Project, Tags 092I and 092F, and the prime correspondence for fibres
(blueprint: lem-exc-weakly-etale-dimension-upper-bound).
-/

@[expose] public section

set_option autoImplicit false

namespace Algebra.WeaklyEtale

/-- A weakly etale algebra has dimension at most that of its base.

Source: Greco, Lemma 5.5, the upper bound in the local AF comparison; Stacks Project,
More on Algebra, Tags 092I and 092F.
(blueprint: lem-exc-weakly-etale-dimension-upper-bound).

Proof: Each residue-field fibre is weakly etale by base change. A field is absolutely
flat, so flatness of tensor multiplication makes that fibre absolutely flat by Tag 092I.
Every prime of the fibre is therefore maximal by Tag 092F. If two comparable primes
of the algebra contract to the same base prime, the order isomorphism between the
spectrum of the fibre and that set of primes identifies them. Thus contraction of
prime ideals is strictly monotone. Applying this map to finite strict chains bounds
all their lengths by the dimension of the base, including unbounded dimension and
the empty spectrum of a zero ring.
-/
theorem ringKrullDim_le {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.WeaklyEtale R S] : ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  intro p q hpq
  refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
  intro heq
  let r := PrimeSpectrum.comap (algebraMap R S) p
  let e := PrimeSpectrum.preimageOrderIsoFiber R S r
  have hp : p ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {r} := rfl
  have hq : q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {r} := by
    exact heq.symm
  have : Ring.AbsolutelyFlat (r.asIdeal.Fiber S) :=
    .of_flat_lmul' r.asIdeal.ResidueField (r.asIdeal.Fiber S)
      (Algebra.WeaklyEtale.flat_lmul' _ _)
  have : Ring.KrullDimLE 0 (r.asIdeal.Fiber S) :=
    (((Ring.AbsolutelyFlat.tfae (r.asIdeal.Fiber S)).out 0 2 rfl rfl).mp
      (inferInstance : Ring.AbsolutelyFlat (r.asIdeal.Fiber S))).2
  have hlt : e ⟨p, hp⟩ < e ⟨q, hq⟩ := e.strictMono hpq
  exact hlt.ne (PrimeSpectrum.ext
    ((Ideal.isMaximal_of_isPrime (e ⟨p, hp⟩).asIdeal).eq_of_le
      (e ⟨q, hq⟩).isPrime.ne_top hlt.le))

end Algebra.WeaklyEtale
