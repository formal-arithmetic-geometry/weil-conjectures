/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import WeilConjectures.RingTheory.HenselianPairDomainConnected

/-!
# Connected zero loci over a henselian pair

For a henselian pair `(A, I)` and a prime `p` of `A`, the closed subset `V(p + I)` of `Spec A` is
connected (`PrimeSpectrum.connectedSpace_zeroLocus_sup_of_henselian`).

## Implementation details

The pair `(A ⧸ p, I(A ⧸ p))` is henselian since `A ⧸ p` is integral over `A`, so the domain case
`connectedSpace_zeroLocus_of_henselian_domain` applies; `V(p + I)` is the image of the
corresponding closed subset of `Spec (A ⧸ p)`.

## References

* [Stacks, Tag 09Y6]
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- For a henselian pair `(A, I)` and a prime ideal `p`, the closed subset `V(p + I)`
is connected in its subspace topology, including nonemptiness. -/
theorem connectedSpace_zeroLocus_sup_of_henselian {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] (p : Ideal A) [p.IsPrime] :
    ConnectedSpace (zeroLocus ((p ⊔ I : Ideal A) : Set A)) := by
  have : HenselianRing (A ⧸ p) (I.map (algebraMap A (A ⧸ p))) :=
    henselianRing_of_isIntegral A I (A ⧸ p)
  have hconn := isConnected_iff_connectedSpace.mpr
    (connectedSpace_zeroLocus_of_henselian_domain (I.map (algebraMap A (A ⧸ p))))
  have himage := hconn.image (comap (Ideal.Quotient.mk p))
    (continuous_comap _).continuousOn
  apply isConnected_iff_connectedSpace.mp
  simpa [Ideal.Quotient.algebraMap_eq,
    image_comap_zeroLocus_eq_zeroLocus_comap (A ⧸ p) (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm] using himage

end PrimeSpectrum
