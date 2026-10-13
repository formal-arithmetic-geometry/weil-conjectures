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

Source: Stacks Project, Algebra, Lemma 10.39.18 (Tag 00HT), part (6), only-if direction
(blueprint: lem-pc-affine-flat-module-local-criterion).
-/

@[expose] public section

namespace Module.Flat

/-- Stacks Project, Algebra, Lemma 10.39.18 (Tag 00HT), part (6), only-if direction
(blueprint: lem-pc-affine-flat-module-local-criterion). Fix `q` and contract it to `p` in `R`.
Localizing the `A`-module `M` away from `q` preserves its flatness over `R` by
`lem-pc-affine-flat-module-localization-preserves-flatness`. Every element outside `p`
maps to a unit in `A_q`, giving `M_q` its `R_p`-module structure. Finally,
`lem-weil-pbc-flat-over-localization` identifies flatness of this module over `R` with
flatness over `R_p`. -/
theorem localizedModule_atPrime_of_flat {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommMonoid M] [Module A M] (q : Ideal A) [q.IsPrime]
    (hflat : @Module.Flat R M _ _ (Module.compHom M (algebraMap R A))) :
    @Module.Flat (Localization.AtPrime (q.comap (algebraMap R A)))
      (LocalizedModule q.primeCompl M) _ _
      (Module.compHom _ (Localization.localRingHom (q.comap (algebraMap R A)) q
        (algebraMap R A) rfl)) := sorry

end Module.Flat
