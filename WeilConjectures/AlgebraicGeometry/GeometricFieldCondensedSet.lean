/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Condensed.Equivalence
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite

/-!
# The pro-étale topos of a separably closed field is the topos of condensed sets

Let `Ω` be a separably closed field. Profinite sets form a dense subsite of the pro-étale site of
`Spec Ω` via `S ↦ (Spec Ω)[S]`
(`AlgebraicGeometry.ProEtale.geometricFieldProfiniteDenseSubsite`), so restriction along this
functor identifies sheaves of sets on `(Spec Ω)_proét` with condensed sets
(`AlgebraicGeometry.ProEtale.geometricFieldSheafEquivCondensedSet`, blueprint
`proposition-pro-etale-site-separably-closed--2`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- For a separably closed field `Ω`, the topos of the pro-étale site of `Spec Ω` is the topos
of condensed sets (with the set-theoretic cutoff given by the universe `u` of `Ω`): restriction
along the dense subsite `S ↦ (Spec Ω)[S]` of profinite sets, followed by the equivalence between
coherent sheaves on profinite sets and on compact Hausdorff spaces.
(blueprint: `proposition-pro-etale-site-separably-closed--2`) -/
noncomputable def geometricFieldSheafEquivCondensedSet :
    Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) (Type (u + 1)) ≌ CondensedSet.{u} :=
  have := geometricFieldProfiniteDenseSubsite Ω
  ((profiniteToProEtOf (Spec (.of Ω))).sheafPushforwardContinuous (Type (u + 1))
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology (Spec (.of Ω)))).asEquivalence.trans
    (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1)))

end AlgebraicGeometry.ProEtale
