/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedGenericScalarModelData

/-! # Lifting lisse objects through a normalized component corner

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Proposition 4.3(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGenericScalarModel

/-- Any normalized component corner on a w-contractible affine lifts lisse objects.

Source: HRS Proposition 4.3(3), construction (4.1)
(blueprint: lem-zl-condensed-contractible-corner-lisse-lift).

Proof: w-contractible lisse evaluation gives the component equivalence on dualizable
objects, with its canonical coefficient comparison. Compare the corner's inverse
image with that functor using inverse_eq and the uniqueness of adjunction mates.
The absolute-test projection normalization identifies the two beta comparisons:
their right-adjoint mates are restriction along the same test-object isomorphism.
The coefficient_eq field then identifies their coefficient transports. Lift this
comparison to ordinary module functors and derive it termwise. Apply essential
surjectivity of the lisse equivalence to N. The inverse object is dualizable, and
the equivalence counit composed with the comparison gives the required isomorphism.
For the empty affine or zero ring both categories have only zero objects. -/
theorem contractible_corner_lisse_lift
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
    (c : ComponentDerivedSquare.Corner Λ T)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)))
    (hN : Nonempty (HasRightDual N)) :
    ∃ M : CondensedRing.Evaluation.D
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace T)),
      Nonempty (HasRightDual M) ∧ Nonempty ((c.derived Λ T).obj M ≅ N) := by sorry

end AlgebraicGeometry.ProEtale.CondensedGenericScalarModel
