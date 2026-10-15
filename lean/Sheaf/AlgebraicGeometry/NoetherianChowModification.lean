/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# A projective modification of a reduced proper scheme

Source: Weil conjectures blueprint, `sec-smooth-purity`, `sk-prop-sf-cbc`,
`lem-fin-noetherian-chow-modification`; Stacks Project, Tag 0200.
(blueprint: lem-fin-noetherian-chow-modification)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A reduced proper scheme over an affine Noetherian base has a proper modification,
projective over the base, which is an isomorphism over a dense open subset.

Source: Weil conjectures blueprint, `sk-prop-sf-cbc`,
`lem-fin-noetherian-chow-modification`; Stacks Project, Tags 0200 and 01W8.
(blueprint: lem-fin-noetherian-chow-modification)

Proof: (1) Properness gives separatedness and finite type. Apply
`lem-weil-pbc-chow-noetherian` to obtain a proper surjection π, an immersion i into
finite-dimensional projective space over S, and a dense open U over which π is an
isomorphism. The immersion is over S, so its composite with the projective-space
structure morphism is π followed by f.
(2) By `lem-weil-pbc-proper-composition`, this composite is proper. The projective-space
structure morphism is proper by `lemma-nagata-projective-space-base-change-proper`,
hence separated. Thus `lem-weil-pbc-proper-over-separated` makes i proper, and
`lem-weil-pbc-proper-immersion-closed` makes it a closed immersion.
(3) This closed immersion witnesses H-projectivity of π followed by f. Its properness
also gives finite type and hence quasi-compactness (`def-weil-finite-type-morphism`).
Together these give projectivity in `def-pc-projective-morphism`. Retain π and U
from step (1) for the remaining conclusions. -/
theorem exists_projective_modification_of_isAffine_isNoetherian
    {S X : Scheme.{u}} [IsAffine S] [IsNoetherian S] (f : X ⟶ S)
    [IsProper f] [IsReduced X] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (U : X.Opens),
      IsProper π ∧ Dense (U : Set X) ∧ IsIso (π ∣_ U) ∧ IsProjective (π ≫ f) := by
  sorry

end AlgebraicGeometry
