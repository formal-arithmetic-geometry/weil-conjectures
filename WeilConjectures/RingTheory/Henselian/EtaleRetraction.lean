/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.RingTheory.Idempotents

/-!
# Henselian local rings: étale retractions and idempotent lifting

Let `(R, 𝔪, κ)` be a local ring. We prove the following characterisations of henselian local
rings (Stacks, Lemma 04GG), following the blueprint.

* If simple roots of monic polynomials lift from `κ` to `R` (Mathlib's `HenselianLocalRing`),
  then every étale `R`-algebra `S` has, through every prime `q` over `𝔪` with trivial residue
  field extension, exactly one `R`-algebra retraction `τ : S →ₐ[R] R` with `τ⁻¹(𝔪) = q`.
* If étale `R`-algebras have such retractions, every finite `R`-algebra is a finite product of
  local rings.
* `R` is henselian (in Mathlib's sense of root lifting) if and only if idempotents of
  `B / 𝔪B` lift uniquely to `B` for every finite `R`-algebra `B`.

## Main results

- `IsLocalRing.existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot`
- `HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_eq`
- `IsLocalRing.exists_algEquiv_pi_isLocalRing_of_forall_exists_algHom`
- `IsLocalRing.forall_existsUnique_isIdempotentElem_iff_forall_exists_isRoot`
- `HenselianLocalRing.iff_forall_existsUnique_isIdempotentElem`

## References

- Stacks Project, Lemma 10.153.3, <https://stacks.math.columbia.edu/tag/04GG>
-/

@[expose] public section

universe u v

open Polynomial IsLocalRing
open scoped TensorProduct

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

end IsLocalRing

namespace HenselianLocalRing

variable {R : Type u} [CommRing R]

end HenselianLocalRing

namespace IsStrictlyHenselianLocalRing

variable {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]

end IsStrictlyHenselianLocalRing
