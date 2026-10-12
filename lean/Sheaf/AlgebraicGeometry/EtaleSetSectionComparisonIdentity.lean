/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Identity calculation for étale section comparisons

Source: Stacks Project, Sites Tags 03CB and 03CC, and Étale Cohomology Tag 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The scheme-level identity calculation, before specializing to a diagram.

Source: Stacks Project, Sites Tags 03CB and 03CC (composition of morphisms of sites),
with the identity adjunction and fibre-product pasting as in Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-section-comparison-identity).

Proof: identify base change by the identity of `S` with the identity functor using
`MorphismProperty.Over.pullbackId`. Restriction along this isomorphism identifies the
right adjoint with the identity. Uniqueness of left adjoints therefore identifies
inverse image by the identity with the identity, compatibly with its adjunction unit.
For the fixed sheaf `G`, the composition of this identification on the inverse image
by `f` with the inverse-image composition isomorphism has the same unit equation as
the identity morphism of that inverse image: naturality of the identity identification
moves the `f`-unit through it, and the two identity fibre-product identifications cancel.
The fixed-sheaf uniqueness clause of `etaleSetInverseImageCompositionUnits` identifies
these sheaf morphisms. Evaluate at the base change of `U` by `f`. In the definition of
`etaleSetSectionComparison`, the remaining unit and restriction along the identity
pasting isomorphism cancel by the unit-compatible identity adjunction. Equality
transport is independent of its proof. Thus the resulting section map is the identity.
This argument also works for an empty scheme or a sheaf with no sections: it is an
identity of sheaf morphisms, evaluated at an arbitrary site object. -/
theorem etaleSetSectionComparisonIdentity
    {R S : Scheme.{u}} (f : S ⟶ R)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    etaleSetSectionComparison (𝟙 S) f f (Category.id_comp f) G U = 𝟙 _ := by sorry

end AlgebraicGeometry
