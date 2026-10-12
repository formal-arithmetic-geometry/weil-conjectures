/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleRestrictedTotalConstruction
public import Mathlib.CategoryTheory.Subobject.FactorThru

/-! # Properties of the restricted augmented CE total

Source: Stacks Project, Tags 015J and 0133.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical sections inclusion factors through the filtered step.
Source: Stacks, Tag 015J, proof remark (3), column filtration.

Proof: In each degree the restricted mapped total is the coproduct of the
summands with complex degree s ≥ q. Its map to the full mapped total is their
coproduct inclusion. Thus its image is the second-filtration subobject at q.
T.filtration_formula identifies this with (T.L).complexStep q n. The canonical
finite-diagonal sections comparison identifies Γ of the restricted sheaf total
with this restricted mapped total. Factor its inclusion degreewise through the
step inclusions. These maps commute with differentials: after composing with
the monic step inclusion the equation is the chain-map equation for the total
inclusion. Thus they assemble into a factorization through (T.L).step q.
In empty diagonals all maps are zero; no positivity assumption on q is used.
(blueprint: lem-weil-pbc-etale-restricted-sections-factors). -/
theorem etaleRestrictedSections_factors
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    (T.L.step q).Factors (etaleRestrictedSectionsInclusion X K T q) := by
  sorry

end AlgebraicGeometry.Etale
