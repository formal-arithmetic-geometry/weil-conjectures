/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Characteristic zero at the generic points of logarithmic strata

Source: ILO, Travaux de Gabber, VIII 3.4.14--3.4.15
(blueprint: def-per-characteristic-zero-log-strata).

The strata are the connected components of the constant-rank loci of the
geometric characteristic group. Their generic points are taken in the
subspace topology, with no assumption that a stratum is closed in the scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The constant-rank locus is defined using the rank of the characteristic group
at every geometric point above the specified ordinary point. This does not use
Zariski stalks when the log structure is only etale local.
Source: ILO VIII 3.4.14--3.4.15
(blueprint: def-per-characteristic-zero-log-strata). -/
def logCharacteristicRankLocus (X : FineSaturatedLogScheme.{u}) (r : ℕ) : Set X.scheme :=
  {x | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
    t default = x → X.logStructure.characteristicRank t = (r : ℕ∞)}

/-- Generic points of every connected component of every constant-rank locus
have characteristic zero. The generic-point condition uses the topology of the
rank locus itself, so locally closed strata need not be closed in the scheme.
Source: ILO VIII Theorem 3.4.15
(blueprint: def-per-characteristic-zero-log-strata). -/
def HasCharacteristicZeroLogStrata (X : FineSaturatedLogScheme.{u}) : Prop :=
  ∀ (r : ℕ) (x : logCharacteristicRankLocus X r),
    IsGenericPoint x (connectedComponent x) → CharZero (X.scheme.residueField x.1)

end AlgebraicGeometry
