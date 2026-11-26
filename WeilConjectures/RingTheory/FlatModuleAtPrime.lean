/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness

/-!
# Flat modules localized at a prime of an algebra

If an `A`-module `M` is flat over `R`, then its localization at a prime `q` of `A` is flat over
the localization of `R` at the contraction of `q`.

## Implementation details

Localization preserves flatness over `R`; elements outside `p` act invertibly on `M_q`, so
flatness over `R` is equivalent to flatness over `R_p`.

## References

* [Stacks, Tag 00HT], part (6), only-if direction
-/

@[expose] public section

namespace Module.Flat

/-- If an `A`-module `M` is flat over `R`, then for a prime `q` of `A` contracting to `p` in
`R`, the localization `M_q` is flat over `R_p`. -/
theorem localizedModule_atPrime_of_flat {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommMonoid M] [Module A M] (q : Ideal A) [q.IsPrime]
    (hflat : @Module.Flat R M _ _ (Module.compHom M (algebraMap R A))) :
    @Module.Flat (Localization.AtPrime (q.comap (algebraMap R A)))
      (LocalizedModule q.primeCompl M) _ _
      (Module.compHom _ (Localization.localRingHom (q.comap (algebraMap R A)) q
        (algebraMap R A) rfl)) := by
  let : Module R M := Module.compHom M (algebraMap R A)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
  have : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let p := q.comap (algebraMap R A)
  let Rp := Localization.AtPrime p
  let Mq := LocalizedModule q.primeCompl M
  let : Module Rp Mq := Module.compHom Mq
    (Localization.localRingHom p q (algebraMap R A) rfl)
  have hloc : Module.Flat R Mq := localizedModule_of_algebra q.primeCompl hflat
  have : IsScalarTower R Rp Mq := by
    constructor
    intro r s m
    change Localization.localRingHom p q (algebraMap R A) rfl (r • s) • m =
      r • (Localization.localRingHom p q (algebraMap R A) rfl s • m)
    rw [Algebra.smul_def, map_mul, Localization.localRingHom_to_map, mul_smul]
    rw [IsScalarTower.algebraMap_smul (R := A) (A := Localization.AtPrime q)]
    rw [IsScalarTower.algebraMap_smul (R := R) (A := A)]
  exact (Module.flat_iff_of_isLocalization Rp p.primeCompl Mq).mpr hloc

end Module.Flat
