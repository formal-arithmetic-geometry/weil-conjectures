/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.RingTheory.Etale.QuasiFiniteAtPrime
import Sheaf.RingTheory.QuasiFiniteLocalDimension
import Sheaf.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom

/-!
# Local dimension under an étale ring map

Source: Stacks Project, More on Algebra, Lemma Tag 07QP
(blueprint: lem-sc-etale-local-dimension).
-/

@[expose] public section

universe u v

namespace RingHom.Etale

/-- Localizing an étale ring map at a prime and its contraction preserves Krull dimension.
Source: Stacks Project, More on Algebra, Lemma Tag 07QP
(blueprint: lem-sc-etale-local-dimension).

Proof: The induced map on localizations is flat and local
(`lem-weil-pbc-etale-algebra-flat`, `lem-weil-pbc-flat-local-ring-maps`), hence faithfully flat
(`lem-pc-local-flat-faithful-flat-reflects-surjective`). Going down yields the lower bound
`dim A_p ≤ dim B_q` (`lem-sc-faithfully-flat-local-dimension`).
For the reverse bound, the étale map is of finite type and quasi-finite at `q`
(`lem-weil-pbc-etale-ring-map-quasi-finite`). Apply the quasi-finite local dimension inequality
(`lem-weil-pbc-dimension-inequality-quasi-finite`) to obtain `dim B_q ≤ dim A_p`.
Antisymmetry gives the asserted equality. -/
theorem ringKrullDim_localization_eq {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Etale) (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime (Ideal.comap f q)) =
      ringKrullDim (Localization.AtPrime q) := by
  sorry

end RingHom.Etale
