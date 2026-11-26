/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.FlatUnderRegular

/-!
# Regularity descends along faithfully flat ring maps

If `R → S` is faithfully flat and `S` is regular, then `R` is regular.

## Implementation details

`R` is Noetherian by faithfully flat descent. Each prime `p` of `R` lies under a prime `q` of
`S`, and `R_p → S_q` is a flat local map of Noetherian local rings with regular target, so
`R_p` is regular.

## References

* [Stacks, Tag 07NG]
-/

@[expose] public section

universe u v

namespace IsRegularRing

/--
If a homomorphism of commutative rings `R → S` (the structure map of `[Algebra R S]`) is
faithfully flat and its target is regular, then its source is regular, hence Noetherian.
-/
theorem of_faithfullyFlat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IsRegularRing S] :
    IsRegularRing R := by
  have : IsNoetherianRing R :=
    Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (R := R) (A := S) (M := R)
      (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid R S S).symm.toLinearEquiv)
  refine ⟨fun p hp ↦ ?_⟩
  obtain ⟨q, hq⟩ :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) ⟨p, hp⟩
  have hpq : p = Ideal.comap (algebraMap R S) q.asIdeal :=
    (congrArg PrimeSpectrum.asIdeal hq).symm
  exact IsRegularLocalRing.of_ringHom_flat
    (Localization.localRingHom p q.asIdeal (algebraMap R S) hpq)
    ((RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S)).localRingHom
      q.asIdeal p hpq)

end IsRegularRing
