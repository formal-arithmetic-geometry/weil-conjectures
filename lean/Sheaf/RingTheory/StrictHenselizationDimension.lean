/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.RingTheory.Etale.LocalDimension
import Sheaf.RingTheory.FilteredColimitPrimeChainDimension
import Sheaf.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom
import Sheaf.RingTheory.StrictHenselizationFaithfullyFlat
import Sheaf.RingTheory.StrictHenselizationTriples

/-!
# Krull dimension of a strict henselization

Source: Stacks Project, More on Algebra, Tag 06LK
(blueprint: lem-sc-strict-henselization-dimension).
-/

@[expose] public section

universe u

namespace Algebra

/-- Strict henselization preserves the Krull dimension of any local commutative ring.
Here `C` is the strict henselization of `R` with respect to the separable closure `K` of
the residue field of `R`.
Source: Stacks Project, More on Algebra, Tag 06LK
(blueprint: lem-sc-strict-henselization-dimension).

Proof: The canonical local map is faithfully flat
(lem-sc-strict-henselization-faithfully-flat), so going down gives the lower bound
(lem-sc-faithfully-flat-local-dimension). For the upper bound, use the filtered étale
triples presentation (lem-weil-pbc-strict-henselization-triples). Every finite strict
chain of primes contracts to a strict chain in some stage
(lem-sc-filtered-colimit-prime-chain-dimension). All contracted primes lie below the
pointed prime at that stage, so the chain survives in its localization. Étale local
dimension invariance (lem-sc-etale-local-dimension) identifies that localization's
dimension with that of `R`. Every finite chain length is therefore bounded by
`ringKrullDim R`, which gives the upper bound, including when the dimension is infinite. -/
theorem ringKrullDim_eq_of_isStrictHenselization
    (R K C : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C] (hC : IsStrictHenselization R K C) :
    ringKrullDim R = ringKrullDim C := by
  sorry

end Algebra
