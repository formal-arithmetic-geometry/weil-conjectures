/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicCompletedTensorCommonComponent

/-! # Naturality of the explicit completed tensor components

Source: BS Remark 6.8.15; HRS Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.AdicQbarRealization.ordinary

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

/-- Naturality of the explicitly constructed common-field tensor comparison.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Proposition 5.2 and Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-component-naturality).

Proof: first fix one finite coefficient field. On constructible integral objects,
the tensor comparison is the composite of the integral realization comparison,
the inverse ordinary tensor comparison, the quotient-completion comparison, and
the integral-to-rational tensor identification. Each of these squares is natural:
the first two are natural isomorphisms, the third is the natural completion map,
and the fourth follows from the prescribed bilinear action of rational tensor.
Thus their composite commutes with every pair of integral arrows.

For an inclusion of finite coefficient fields, choose good K-flat representatives
of both inputs. Use the representative equation of each finite model to express
its ordinary tensor map through its universal scalar-extension counits. These
counits are invertible on the chosen representatives by the recorded K-flatness.
Use the normalized completion model to replace its quotient comparison by the
fixed completion map. After cancellation, the coefficient-extension square is
the square for the balanced total-complex scalar comparison. In every bidegree,
the balance_sections equations give the same image of a pure tensor: the two
coefficient scalars are multiplied and the two module sections are retained.
Pure tensors generate the presheaf tensor products, their images generate the
sheafified tensor products locally, and the totalization coproduct injections
jointly detect maps. Hence the square commutes as a complex map. The universal
counits descend it to the derived category, and the good-model comparisons
transport it to the original integral objects. The common_field equation of R
identifies its outer scalar comparisons with the actual isoToStage maps.

In the raw scalar localization, any morphism is a finite sum of localized
integral morphisms. Naturality extends from integral morphisms to these sums:
additivity treats sums, while for a denominator power the naturality square for
its integral multiple can be cancelled because that power is invertible. This
applies in each tensor variable. Finally represent both common-stage arrows at
one finite coefficient field containing the stages of all four endpoints.
The coefficient-extension squares just proved transport both component formulas
to that field. The normalized stageTensor inclusion formula and the prescribed
representative formula for commonStageDerivedTensor then reduce the desired
equality to finite-field naturality. Cancelling the
endpoint isoToStage comparisons proves the displayed equality. This argument
also covers zero objects, zero arrows, coincident stages, and an empty scheme. -/
theorem completedTensorCommonComponent_naturality
    (symmetry : @SymmetricCategory _ _ closed.monoidal)
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    {P Q : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ×
      generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X}
    (f : P ⟶ Q) :
    (((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor).map f ≫
        (completedTensorCommonComponent l X R closed models N Q.1 Q.2).hom =
      (completedTensorCommonComponent l X R closed models N P.1 P.2).hom ≫
        (commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R).map f := by sorry

end WeilConjectures.AdicQbarRealization
