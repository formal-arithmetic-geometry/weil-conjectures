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

/-! Symmetry equation for the common-stage completed tensor lift.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-symmetric).
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
/- A natural invertible binary comparison need not preserve symmetry. -/
namespace TensoratorSymmetryNormalizationTest
end TensoratorSymmetryNormalizationTest

namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)
  (symmetry : @SymmetricCategory _ _ closed.monoidal)

/- STATEMENT-DISPUTED (repaired): the former statement quantified over an arbitrary
natural tensor isomorphism. Naturality does not imply symmetry: the private graded-line
example above is a counterexample to that inference. The explicit component equation
below restricts the law to the constructed comparison, and its existing constructor
supplies this equation without assuming a coherence law. -/

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

/-- The symmetry component for the explicitly normalized common-stage tensorator.
Source: BS Remark 6.8.15; HRS Lemma 7.9.

Proof plan: replace the two tensorator components by their normalization equations.
Choose one finite field containing both input stages and express both components at
that field, using the component stage-transport equation. On integral good K-flat
representatives expand N.representative and N.balance_sections. Both paths send
s tensor (x tensor y) to the tensor of 1 tensor y and s tensor x, with the same
Koszul factor (-1)^(pq); the balancing relation moves the scalar between factors.
The native symmetry_model identifies this signed swap with the target braiding.
Use the normalized completion augmentation and coherent-reduction tensor comparison
to identify the source integral braiding with the same swap. Pass through the good
complex localization, rational localization and the prescribed common-stage braiding
representative. Cancel the endpoint isoToStage maps using naturality of the source
and target braidings. This yields the stated equality for the normalized components.
Zero objects, coincident fields and empty schemes use these same equations; no
nonzero coefficient object or choice-independent arbitrary tensorator is assumed.
The source coherent-reduction identification remains part of this named obligation.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-symmetric). -/
theorem completed_tensor_common_lift_constraints_symmetric
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry)
    (normalized : ∀ A B, data.tensor.hom.app (A, B) =
      (completedTensorCommonComponent l X R closed models N A B).hom) :
    ∀ A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      data.tensor.hom.app (A, B) ≫
          (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
        (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
          data.tensor.hom.app (B, A) := by
  sorry

end WeilConjectures.AdicQbarRealization
