/-
Copyright (c) 2026 The SHEAF contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Ordinary-to-completed tensor and the adjoint comparison

Source: the normalized completion and evaluation argument in
thm-coef-rational-verdier.proof.md, paragraph 1
(blueprint: lem-sf-ordinary-completed-tensor-adjoint-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The counit-preserving comparison of the ordinary left tensor with the canonical
right tensor commutes with the actual completion maps and signed braiding.
Source: thm-coef-rational-verdier.proof.md, paragraph 1; the normalized completion
and tensor-Hom evaluation argument, Stacks 08J9, 07A4, 099B.
Proof: compare the two ordinary tensors on K-flat representatives. Their tensor-Hom
counits have the same signed Hom-complex evaluation on every homogeneous local
pure tensor. Thus the comparison preserving those counits, namely leftAdjointUniq,
is the ordinary signed interchange followed by the tensor model comparison.
The completion representative equation identifies its composite with the actual
completion unit: both have the quotient image of each pure tensor in the first
Roos coordinate and zero in the shifted coordinate. The completed braiding has
exactly the corresponding signed interchange after coherent reduction. Faithful
coherent reduction and the K-flat localization extend the equality to all integral
constructible inputs. The construction also covers zero inputs and empty schemes.
(blueprint: lem-sf-ordinary-completed-tensor-adjoint-square). -/
theorem ordinaryCompletedTensor_adjoint_square
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (c : RationalVerdier.Completion D l hl X E a)
    (K N : sfIntegralConstructibleCategory l E X) :
    ((a.adjunction K.obj).leftAdjointUniq
      ((pullbackTensorCalculus l E X).integralClosed.adjunction K.obj)).hom.app N.obj ≫
        podCompletedTensorUnit l E X N.obj K.obj =
      c.map.app (K.obj, N.obj) ≫
        (@pullbackTensorIntegralBraiding l _ E _ _ _ X
          (RationalVerdier.units D l hl X) K N).hom.hom := by
  sorry

end WeilConjectures.RationalOperations
