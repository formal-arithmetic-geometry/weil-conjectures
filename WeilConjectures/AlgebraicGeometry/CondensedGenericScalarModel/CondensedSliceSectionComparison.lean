/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedGenericScalarModelData

/-! # Normalized inverse-image comparisons for a profinite section

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes,
Theorem 4.13, paragraph following diagram (4.4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGenericScalarModel

/-- A section of a profinite map supplies the normalized module and scalar comparisons.

Source: HRS Theorem 4.13, paragraph following diagram (4.4), Remark 3.2
(blueprint: lem-zl-condensed-slice-section-comparison).

Proof: construct the slice inverse image along s by sheafified left Kan extension
along Over.pullback s. Its standard adjunction and monoidal structure give the
canonical Slice data; the absolute-test base-change isomorphism gives beta.
Since s followed by r is the identity, the iterated test pullback is naturally
isomorphic to the identity, with underlying map the two first projections.
Take its adjunction mate to obtain abelian; the conjugate equality is the stated
abelian_mate. The coefficient restrictions are all from the same Lambda, so lift
abelian to the ordinary module comparison, with the same underlying map.
Similarly lift inverse.beta to the scalar module comparison. Naturality and
monoidality verify linearity. These constructions give all fields of
SectionComparison with their specified underlying maps. Empty profinite spaces
and the zero ring require no separate choices. -/
theorem slice_section_comparison
    (Λ : Profinite.CondensedRing.{u})
    {S V : Profinite.{u}} (r : V ⟶ S) (s : S ⟶ V)
    (hs : s ≫ r = 𝟙 S) (restriction : ComponentDerivedSquare.Slice Λ r) :
    Nonempty (SectionComparison Λ r s restriction) := by sorry

end AlgebraicGeometry.ProEtale.CondensedGenericScalarModel
