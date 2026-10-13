/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.ScalarGlobalSectionsComparison

/-! # Pullback in degree zero on global sections

Source: Stacks Project, Cohomology, Tags 01DZ, 0FKV; Modules, Tag 0096.
(blueprint: lem-sc-scalar-pullback-zero-global-sections).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- Degree-zero cohomology pullback evaluates to the tensor-pullback unit on sections.
Source: Stacks Project, Cohomology, Tags 01DZ, 0FKV; Modules, Tag 0096.
(blueprint: lem-sc-scalar-pullback-zero-global-sections).

Proof: The cocycle formula specifying moduleExtEquiv in degree zero identifies
the rightDerivedZeroIsoSelf global section with evaluation at 1 of the unique
morphism from the structure sheaf representing the degree-zero Ext class.
After restriction of scalars and precomposition with scalarUnitMorphism, the
constant-sheaf adjunction identifies the resulting scalar-unit morphism with
that same global section. Represent scalarCohomologyExtEquiv f F 0 x by mk₀
of this morphism. Exact inverse image sends mk₀ to the degree-zero class of
its inverse-image morphism, and composing with mk₀ classes is ordinary morphism
composition. Precomposition with scalarInverseUnitIso.inv identifies the
inverse-image constant unit with the target constant unit. Postcomposition with
scalarPullbackCoefficient is adjoint to the sectionwise tensor-pullback unit,
by Classical.choose_spec of exists_scalarPullbackCoefficient. Apply that
adjunction identity to the top open. Its inverse image is the top open on Y;
the restriction along the canonical inclusion of the top open into its inverse
image is the one in tensorPullbackTopSection. Finally cancel the target
scalarCohomologyExtEquiv with its inverse in scalarCohomologyPullback. No
quasi-coherence or nonemptiness is used, and the formula sends zero to zero. -/
theorem scalarCohomologyPullback_zero_globalSections
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : X.Modules) (x : scalarCohomology f F 0) :
    scalarGlobalSectionsEquiv g ((tensorPullback a).obj F)
        (scalarCohomologyPullback f g a h F 0 x) =
      tensorPullbackTopSection a F (scalarGlobalSectionsEquiv f F x) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
