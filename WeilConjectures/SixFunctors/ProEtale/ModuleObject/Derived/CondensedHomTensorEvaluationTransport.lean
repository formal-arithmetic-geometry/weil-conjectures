/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom

import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions

/-! # Tensor-evaluation transport for condensed scalar Hom

Source: current blueprint `part-duality-trace-formula/sec-lefschetz-verdier/`
`sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/`
`lem-fix-operation-reduction.proof.md`, paragraphs 1 and 3: the specified coefficient
comparison is adjoint to tensoring evaluation.
(blueprint: lem-sf-finite-quotient-hom-tensor-evaluation-transport).

All operations take place in the native ordinary unbounded derived categories of
internal modules over the pulled-back condensed rings. The canonical scalar tensorator
already includes its K-flat representative normalization. A natural isomorphism `e`
allows any other presentation of this scalar functor, including a quotient presentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal brownHypothesesSheafBraided
  brownHypothesesCoefficientMonObj brownHypothesesModuleMonoidalClosed
attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

set_option maxHeartbeats 1200000 in
/-- The transpose of the specified scalar Hom comparison, transported through `e`
in both Hom arguments, is the tensor of `e` inverse with the identity, followed by
the inverse normalized tensorator, scalar extension of evaluation, and `e` on the target.
Here the native closed adjunction uses left evaluation, so the tensor order is
`T P` followed by `F RHom(P,Q)`; the right-evaluation version is obtained by symmetry.
No perfectness, boundedness, or flatness assumption is required for this equation.

Source: current blueprint `lem-fix-operation-reduction.proof.md`, paragraphs 1 and 3.
(blueprint: lem-sf-finite-quotient-hom-tensor-evaluation-transport).

Proof: compute the inverse closed transpose using its evaluation counit. Naturality
of evaluation in the first argument moves `e.inv.app P` to the tensor factor, and
naturality in the second moves `e.hom.app Q` to the final factor. The evaluation
identity for the specified scalar Hom comparison identifies the middle composite
with inverse scalar tensorator followed by scalar extension of source evaluation.
This tensorator is the canonical derived scalar tensorator: on simultaneous flat-term
K-flat representatives it is the ordinary scalar tensor square. Its localization
normalization therefore supplies the same tensorator for all derived inputs.
Reassociate these composites to obtain the displayed equality. -/
theorem condensedHomTensorEvaluationTransport
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (W : Scheme.{u})
    (T : NativeScalarCategory Λ W ⥤ NativeScalarCategory Λ' W)
    (e : scalarSixChange a W ≅ T) (P Q : NativeScalarCategory Λ W) :
    ((derivedTensorHomAdjunction Λ'.X (T.obj P)).homEquiv
      ((scalarSixChange a W).obj (((derivedHom Λ.X W).obj (.op P)).obj Q))
      (T.obj Q)).symm
        (scalarSixHomComparison a W P Q ≫
          ((derivedHom Λ'.X W).map (e.inv.app P).op).app
            ((scalarSixChange a W).obj Q) ≫
          ((derivedHom Λ'.X W).obj (.op (T.obj P))).map (e.hom.app Q)) =
      (e.inv.app P ⊗ₘ
        𝟙 ((scalarSixChange a W).obj (((derivedHom Λ.X W).obj (.op P)).obj Q))) ≫
      (scalarSixTensorIso a W P (((derivedHom Λ.X W).obj (.op P)).obj Q)).inv ≫
      (scalarSixChange a W).map (nativeScalarEvaluation Λ W P Q) ≫ e.hom.app Q := by
  dsimp only [derivedHom, MonoidalClosed.internalHom, Quiver.Hom.unop_op]
  change MonoidalClosed.uncurry _ = _
  erw [← Category.assoc, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_pre_app]
  have hb := Functor.LaxMonoidal.ihomComparison_ev (scalarSixChange a W) P Q
  change MonoidalClosed.uncurry (scalarSixHomComparison a W P Q) =
      (scalarSixTensorIso a W P (((derivedHom Λ.X W).obj (.op P)).obj Q)).inv ≫
        (scalarSixChange a W).map ((derivedTensorHomAdjunction Λ.X P).counit.app Q) at hb
  rw [hb]
  simp only [scalarSixTensorIso, nativeScalarEvaluation, Iso.symm_inv,
    Functor.Monoidal.μIso_hom, tensorHom_id, Category.assoc, derivedHom,
    MonoidalClosed.internalHom]

end AlgebraicGeometry.ProEtale.CondensedRing
