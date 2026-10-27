/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.ClosedRestrictionSignedData

/-!
# Existence of signed augmented closed-restriction rows

Source: Stacks Project, Tag 09AH supplies the closed units; the alternating
construction is the agent deduction using the deleted-position calculation of Tag 01FG.
(blueprint: lem-sfb-signed-closed-row-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- An individual ordered closed family has its unit-normalized signed augmented row.
No cover or exactness assertion is required.

Source: Stacks Project, proetale.tex, Tag 09AH, and the alternating differential
calculation of cohomology.tex, Tag 01FG; steps 1--3, 7 and the augmentation part of
step 8 of lem-sfb-closed-restriction-signed-refinements.
(blueprint: lem-sfb-signed-closed-row-exists).

Proof: form the finite intersections as products over X. For an inclusion s ⊆ t,
the projections give the closed map from the t-intersection to the s-intersection.
Push forward its actual adjunction unit, using the inverse-image compositor for the
coefficient rings. Put zero for pairs not related by inclusion. The composition-unit
identity gives restriction_unit and restriction_comp. For nonempty s the factorization
through Z gives fromSupport by the same construction, with its two unit equations.
Inverse image and direct image are additive, as are finite biproducts. Use the existing
finiteClosedTerms and finiteClosedDifferential to build the row, zero in negative
degrees and degrees at least the family length. Each pair of deleted positions in d²
has equal restriction composite and opposite signs, so it cancels. This also proves
that the singleton augmentation followed by d is zero. It defines alpha from the
single complex, with the required degree-zero component. Naturality of units makes
these constructions additive and natural in the module. Applying the augmentation
termwise to a complex and then including its horizontal degree-zero summand defines
totalAugment: the horizontal chain equation and naturality with the input differential
prove its chain equation. Its degree n component is exactly the specified inclusion.
The finite support follows because a strictly increasing (p+1)-tuple cannot exist
when p is at least the family length; the empty product in the additive category is
zero. None of these steps uses the family to cover Z. -/
theorem signedClosedRow_exists {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (F : SignedClosedFamily i) :
    Nonempty (SignedClosedRow i F A) := by sorry

end AlgebraicGeometry
