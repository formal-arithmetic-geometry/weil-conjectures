/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # ScalarCohomologyExtCoefficientNaturality

Source: Stacks Project, Cohomology, Tags 01F7, 01FD, 07MB and 0FKV.
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

attribute [local instance] Sheaf.monoidalCategory HasExt.standard

/-- The recorded cohomology-to-Ext comparison respects coefficient maps.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7.
(blueprint: lem-sc-scalar-cohomology-ext-coefficient-naturality).

Proof: Lift a coefficient morphism to a comparison map of injective resolutions.
The right-derived-functor coefficient map is induced by the global-sections map
of this comparison. Evaluation at 1 identifies the global-sections complex with
Hom from the structure sheaf, naturally in the resolution: every O-linear
comparison map takes the image of 1 to the image of the corresponding section.
The cocycle formula specifying moduleExtEquiv therefore intertwines the derived
coefficient map with postcomposition by the degree-zero Ext class of the
coefficient morphism. Every cohomology class has a cocycle representative, so
this proves naturality of moduleExtEquiv. Exact restriction to scalar sheaves
preserves Yoneda composition and sends the degree-zero coefficient map to
scalarHom. Precompose by scalarUnitMorphism and use associativity of Yoneda
composition. This gives naturality of scalarCohomologyExtMap, hence of its
AddEquiv.ofBijective wrapper scalarCohomologyExtEquiv. This argument applies
also in degree zero and for zero coefficients or the empty scheme.
-/
theorem scalarCohomologyExtEquiv_map
    (f : X ⟶ Spec (CommRingCat.of k)) {F G : X.Modules}
    (φ : F ⟶ G) (n : ℕ) (a : scalarCohomology f F n) :
    scalarCohomologyExtEquiv f G n (scalarCohomologyMap f φ n a) =
      (scalarCohomologyExtEquiv f F n a).comp
        (Abelian.Ext.mk₀ (scalarHom f φ)) (add_zero n) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
