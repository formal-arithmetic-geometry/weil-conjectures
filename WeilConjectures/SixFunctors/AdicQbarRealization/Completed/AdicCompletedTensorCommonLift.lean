/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModels
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLiftAgreement

/-! # Common-stage descent of finite normalized tensor comparisons

Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift).
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
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)
  (symmetry : @SymmetricCategory _ _ closed.monoidal)
  (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)

/-- The common-stage tensorator, its four constraint equations, and agreement
with each of the supplied finite normalized models. The ambient monoidal structure
and finite chain comparisons are inputs, not part of the construction asserted here.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift). -/
structure CompletedTensorCommonLift where
  tensor : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
    commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
  unit : closed.monoidal.tensorUnit ≅
    (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X)
  associative : ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (tensor.hom.app (A, B)) (𝟙 _)) ≫
        tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
        (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
      (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
        ((ordinary l X R).obj C)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (tensor.hom.app (B, C))) ≫
        tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C))
  left_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom unit.hom (𝟙 _)) ≫
        tensor.hom.app (pullbackTensorCommonUnit l (PadicAlgCl l) X, A) ≫
        (ordinary l X R).map (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.leftUnitor ((ordinary l X R).obj A)).hom
  right_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (𝟙 _) unit.hom) ≫
        tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
        (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom
  symmetric : ∀ A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    tensor.hom.app (A, B) ≫
        (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
      (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
        tensor.hom.app (B, A)
  integral_tensor : ∀ E, tensorFiniteAgreement l X R closed tensor E
    (N E).completion (N E).ordinary

/-- Descend already constructed finite normalized comparisons, retaining their
actual components. This statement assumes all finite chain and derived models;
it supplies only the common-stage maps and their coherence.
Source: BS Remark 6.8.15; HRS Lemma 7.9; the original node's steps 2--7.
(blueprint: lem-sf-adic-completed-tensor-common-lift).

Proof:
1. For each E, invert exactly (N E).completion.comparison on constructible pairs
using its normalized final clause. Compose its image under native derived scalar
extension with (N E).ordinary inverse and conjugate by R.integral. This gives the
finite tensorator on integral representatives; the defining composite is precisely
tensorFiniteAgreement. The normalization and representative square of N identify
this map on simultaneous K-flat models, without choosing an unrelated tensorator.
2. On coherent reductions, completedPrimitiveCounitComparison and normalized DVR
effectivity identify the completed constraints with their whole-system tensor
maps. NormalizedTensorConstraintTransport identifies reassociation, both actions
and signed swap even when an inner tensor is re-resolved. IntegralAmbientOperationModels
identifies the quotient augmentation with that of (N E).completion, including its
zero shifted coordinate. To compare the possibly different ordinary tensor
presentations, whisker with the two good-complex localizations and their supplied
model isomorphisms. The representative equations identify both maps there;
fully faithful whiskering then identifies the descended natural transformations.
The balanced pure generators likewise determine the cochain comparison. Thus
arbitrary supplied N give the same normalized finite maps. Combining these
squares with the supplied native coherence proves the four finite constraint equations.
3. For E contained in F, insert the specified inverse finite-free completion
comparison. ScalarExtensionTowerCoherence identifies the tensor comparison with
the balanced whole-tower map. After the augmentations from step 1 both routes
multiply the same scalars. Thus the finite tensorators agree under R.common_field,
including identity and successive extensions, even for ramified fields.
4. Localize the integral Hom modules. Pure rational arrows u tensor a and v tensor b
multiply the integral naturality square by ab; additivity and balancing treat all
arrows. The inverse components localize too. The finite constraint and scalar
squares remain equalities after localization.
5. For two common-stage objects choose a finite field containing their stages.
Use the localized comparison there and conjugate by the actual stage-inclusion
and R.common_field comparisons. Step 3 proves independence under further
extension; any two choices admit a common further field. Represent two arrows at
one further field and use step 4 to prove naturality, independent of arrow
representatives. The same construction on inverse components proves invertibility.
6. Every constraint diagram is represented at one common finite field. Steps 2--4
prove its equality there and step 5 identifies its edges with the common tensorator.
For the unit use coefficient multiplication, whose inverse inserts one. Its two
action equations follow from the same finite balanced maps. The formula of step 1
at each E is the integral_tensor field. Empty X, zero complexes, identity field
extensions and odd-degree swaps require no different construction. -/
theorem completed_tensor_common_lift
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry) :
    Nonempty (CompletedTensorCommonLift l X R closed models symmetry N) := by
  obtain ⟨C⟩ := completed_tensor_common_lift_coherence l X R closed models symmetry N
    coherence
  have hAgreement := completed_tensor_common_lift_agreement l X R closed models symmetry N
    coherence C
  refine ⟨{ tensor := C.tensor
            unit := C.unit
            associative := C.associative
            left_unit := C.left_unit
            right_unit := C.right_unit
            symmetric := C.symmetric
            integral_tensor := hAgreement }⟩

end WeilConjectures.AdicQbarRealization
