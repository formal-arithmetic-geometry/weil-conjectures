/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.RingTheory.NagataLocalization
import Sheaf.RingTheory.GRingOfWeaklyEtale
import Sheaf.RingTheory.LocallyNagataCatenaryOfWeaklyEtale
import Sheaf.RingTheory.NagataJTwoOfWeaklyEtale

/-!
# Excellence ascends along weakly etale ring homomorphisms

Source: Silvio Greco, Two theorems on excellent rings, Nagoya Mathematical Journal 60
(1976), 139–149, Theorem 5.3(iv) and Remark 5.2, pp. 146–147; the Foreword on p. 139
assumes commutative Noetherian rings (blueprint: lem-exc-weakly-etale-excellent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

/-- A Noetherian ring weakly etale over an excellent ring is excellent.

Source: Greco, Two theorems on excellent rings, Theorem 5.3(iv), pp. 146–147, with
Remark 5.2 identifying absolute flatness with flatness of the ring map and of tensor
multiplication (blueprint: lem-exc-weakly-etale-excellent).

Proof:
1. Unpack `hR` using `def-exc-excellent-ring`: `R` is Noetherian, a G-ring, J-2, and
   universally catenary. In particular it is quasi-excellent. Keep the given
   Noetherianity of `S` and weak etaleness of `f` throughout.
2. By `lem-exc-quasi-excellent-nagata`, `R` is Nagata. By the prime-localization
   clause of `lem-weil-pbc-nagata-localization`, every prime localization of `R`
   is Nagata as well. These supply the global and local Nagata hypotheses below.
3. Apply `lem-exc-weakly-etale-g-ring` (Greco 5.3(i), geometric regularity) to `f`:
   the source G-ring property, the two Noetherian conditions, and weak etaleness
   imply that `S` is a G-ring.
4. Apply `lem-exc-weakly-etale-nagata-j2` (Greco 5.3(ii)) with the Nagata and J-2
   properties of `R` and the same map hypotheses. Retain its J-2 conclusion for `S`.
5. Apply `lem-exc-weakly-etale-locally-nagata-catenary` (Greco 5.3(iii)) with the
   prime-local Nagata properties from step 2, universal catenarity from step 1,
   and the unchanged map hypotheses. Retain universal catenarity of `S`.
6. Combine Noetherianity of `S`, its G-ring property, its J-2 property and universal
   catenarity using `def-exc-excellent-ring`. This is `IsExcellent S`, including
   the zero-ring case, where conditions on prime ideals are vacuous. -/
theorem isExcellent_of_weaklyEtale {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hR : IsExcellent R) [IsNoetherianRing S]
    (hf : f.WeaklyEtale) : IsExcellent S := by
  have : IsNoetherianRing R := hR.1.1
  have hNagata := isNagataRing_of_isQuasiExcellent R hR.1
  have hLocallyNagata := (isNagataRing_localization R (⊤ : Submonoid R) hNagata).2.1
  have hGRing := isGRing_of_weaklyEtale f hf hR.1.2.1
  have hJTwo := (isNagataRing_and_jTwo_of_weaklyEtale f hf hNagata hR.1.2.2).2
  have hCatenary :=
    (isUniversallyCatenary_and_locallyNagata_of_weaklyEtale f hf hLocallyNagata hR.2).1
  exact ⟨⟨inferInstance, hGRing, hJTwo⟩, hCatenary⟩

end RingHom
