/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.CategoryTheory.CommAlgebraSheafModule

/-! # Algebra base change compared with module tensor pullback

Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096; Tag 09MS, coefficient quotient.
(blueprint: lem-sc-algebra-tensor-pullback-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Pulling back an algebra sheaf and pushing it forward realizes the unit on its
underlying module, for any supplied tensor-pullback adjunction.

Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096; Tag 09MS, coefficient quotient.
(blueprint: lem-sc-algebra-tensor-pullback-comparison).
Proof: Form the inverse-image algebra sheaf and extend its scalars from the
inverse-image structure sheaf to O_Z by the sheaf tensor product of commutative
algebras. Push this algebra sheaf forward, with structure map induced by j. The
canonical coefficient map is p. Forgetting the ring multiplication commutes with
the inverse image and the sheafified tensor construction: both are sheafifications
of the same sectionwise tensors, with the same restriction maps and O_X actions.
This yields an isomorphism from j_*j^* of the underlying module to the underlying
module of the algebra just constructed. It identifies the canonical tensor unit
with the underlying map of p. For a different supplied adjunction a, use uniqueness
of left adjoints to compare it to the canonical adjunction, apply pushforward to
that comparison, and compose the isomorphism with it. The unit comparison identity
gives the asserted equation. No closed immersion or local freeness is required;
the construction works also for the zero algebra and empty schemes. -/
theorem exists_algebraTensorPullbackComparison {X Z : Scheme.{u}} (j : Z ⟶ X)
    (a : tensorPullback j ⊣ pushforward j) (B : X.CommAlgebraSheaf) :
    ∃ (C : X.CommAlgebraSheaf) (p : B ⟶ C)
      (e : (pushforward j).obj ((tensorPullback j).obj
        (commAlgebraSheafModule X.sheaf B)) ≅ commAlgebraSheafModule X.sheaf C),
      (commAlgebraSheafModuleFunctor X.sheaf).map p =
        a.unit.app (commAlgebraSheafModule X.sheaf B) ≫ e.hom := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
