/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLiftTensorUnit
public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonComponent
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Associativity equation for the common-stage completed tensor lift.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-associative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
/- A generic obstruction explaining why naturality cannot replace normalization. -/
namespace TensoratorNormalizationTest
end TensoratorNormalizationTest

namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)
  (symmetry : @SymmetricCategory _ _ closed.monoidal)

/- The former statement asserted this law for an arbitrary tensorator. The
normalization below fixes the actual common-field comparison; its existence is
proved by completed_tensor_common_lift_normalized_tensor_unit. -/

private structure Line where
  degree : ℤ

private structure Hom (A B : Line) where
  degree_eq : A.degree = B.degree
  scalar : ℚ

private theorem hom_ext {A B : Line} (f g : Hom A B) (h : f.scalar = g.scalar) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def tensor : Line × Line ⥤ Line where
  obj P := ⟨P.1.degree + P.2.degree⟩
  map f := ⟨congrArg₂ (· + ·) f.1.degree_eq f.2.degree_eq, f.1.scalar * f.2.scalar⟩
  map_id _ := hom_ext _ _ (one_mul 1)
  map_comp f g := by
    apply hom_ext
    change (f.1.scalar * g.1.scalar) * (f.2.scalar * g.2.scalar) =
      (f.1.scalar * f.2.scalar) * (g.1.scalar * g.2.scalar)
    ring

private def associator (A B C : Line) :
    tensor.obj (tensor.obj (A, B), C) ≅ tensor.obj (A, tensor.obj (B, C)) where
  hom := ⟨add_assoc A.degree B.degree C.degree, 1⟩
  inv := ⟨(add_assoc A.degree B.degree C.degree).symm, 1⟩
  hom_inv_id := hom_ext _ _ (one_mul 1)
  inv_hom_id := hom_ext _ _ (one_mul 1)

/-- The associativity component of the common-stage constraint system.
The tensorator is explicitly required to have the constructed common-field
components; an arbitrary natural isomorphism does not determine this equation.
Source: BS Remark 6.8.15; HRS Lemma 7.9.

Proof plan: replace every tensorator component by normalized. Choose a coefficient
field containing the stages of the three inputs and their two nested tensor
objects. Use completedTensorCommonComponent_stage_transport and its naturality to
express the four components at that field, cancelling the intermediate isoToStage
maps. Expand the finite components into the quotient-completion comparison and
the inverse ordinary scalar tensor comparison. On good K-flat representatives,
N.representative and N.balance_sections identify each scalar comparison with the
balanced map s tensor (x tensor y) to (s tensor x) tensor (1 tensor y). At triple
pure sections the two composites multiply the same coefficients and reassociate
without a sign. The native coherence.associator_model identifies this chain map
with the target associator. Identify the source associator with its specified
coherent-reduction representative; its rational localization and the prescribed
common-stage representative give the last edge of the left composite. Descend the
chain equality by the good-complex localization, cancel the input and output
comparison isomorphisms, and use the component stage-transport equation to remove
the finite-field choice. Zero complexes, repeated fields and empty schemes use
the same equations. The source-associator identification is part of this remaining
obligation; it is not silently assumed as a consequence of pairwise tensor models.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-associative). -/
theorem completed_tensor_common_lift_constraints_associative
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry)
    (normalized : ∀ A B, data.tensor.hom.app (A, B) =
      (completedTensorCommonComponent l X R closed models N A B).hom) :
    ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      closed.tensor.map (Prod.mkHom (data.tensor.hom.app (A, B)) (𝟙 _)) ≫
          data.tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
          (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
        (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
          ((ordinary l X R).obj C)).hom ≫
          closed.tensor.map (Prod.mkHom (𝟙 _) (data.tensor.hom.app (B, C))) ≫
          data.tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C)) := by
  sorry

end WeilConjectures.AdicQbarRealization
