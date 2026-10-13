/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Scalar and module pullback comparison

Source: Stacks Project, Cohomology, Tag 01F7.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- Scalar and ordinary module pullback have the same underlying cohomology class.
Source: Stacks Project, Cohomology, Tag 01F7, functoriality and independence of lifts.
(blueprint: lem-sc-scalar-module-cohomology-pullback-comparison).

Proof: Choose injective module resolutions and the pushforward comparison used in
moduleCohomologyFMap. Evaluation at 1 identifies module morphisms from the structure
module with sections, so moduleExtEquiv sends a section cycle to its unit morphism.
Exact scalar restriction preserves the underlying cycle and its differential;
precomposition by scalarUnitMorphism is evaluation of the same morphism at 1.
The scalar pullback coefficient is adjoint to the tensor-pullback adjunction unit.
Consequently inverse image on scalar Ext followed by that coefficient is represented
by the same resolution diagram as moduleCohomologyFMap of the unit: the horizontal
map is its lift and the vertical pushforward comparison is inverted on cohomology.
Evaluation at 1 commutes with these maps. Independence of lifts and homotopies
identifies the maps for the choices recorded in the definitions. Transporting back
by scalarCohomologyExtEquiv proves equality on their common underlying carrier.
The argument holds in every natural degree, without quasi-coherence or flatness;
in degree zero it is the adjunction-unit section map. Empty schemes and zero
coefficients give zero classes. -/
theorem scalar_moduleCohomologyPullback_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : X.Modules) (n : ℕ)
    (x : scalarCohomology f F n) :
    scalarCohomologyPullback f g a h F n x = moduleCohomologyPullback a F n x := by sorry

end AlgebraicGeometry.Scheme.Modules
