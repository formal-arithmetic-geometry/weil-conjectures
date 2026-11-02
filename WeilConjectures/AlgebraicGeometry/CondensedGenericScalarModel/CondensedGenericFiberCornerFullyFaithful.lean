/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedGenericScalarModelData

/-! # Full faithfulness of the normalized generic-fibre component corner

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 4.13, diagram (4.4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGenericScalarModel

/-- The component corner on an ind-etale geometric fibre is fully faithful on all
ordinary derived objects.

Source: HRS Theorem 4.13, diagram (4.4) and the paragraph following it
(blueprint: lem-zl-condensed-generic-fiber-corner-fully-faithful).

Proof: base change makes the geometric fibre affine ind-etale over Omega. The
geometric-field component-site comparison identifies its pro-etale topos with the
profinite slice over its actual component space. The inverse image is the relative
test inverse image specified by the corner's inverse_eq. Its absolute-test mate
normalization identifies the coefficient comparison with pullback of Lambda.
Consequently the corner's module functor is an equivalence: lift the inverse
sheaf equivalence to modules using that coefficient isomorphism. It is additive
and exact. Applying it termwise to complexes and localizing quasi-isomorphisms
gives an equivalence of ordinary unbounded derived categories, hence full
faithfulness. An empty fibre is included, with zero coefficient modules. -/
theorem generic_fiber_corner_fully_faithful
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X U : Scheme.{u}} [IsAffine X] [IsAffine U] (f : U ⟶ X)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ X)
    (hind : RingHom.IndEtaleAcrossUniverses f.appTop.hom)
    (c : ComponentDerivedSquare.Corner Λ (pullback f η)) :
    Nonempty (c.derived Λ (pullback f η)).FullyFaithful := by sorry

end AlgebraicGeometry.ProEtale.CondensedGenericScalarModel
