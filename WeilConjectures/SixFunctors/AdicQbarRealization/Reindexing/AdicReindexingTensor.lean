/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingTensorCompatibility
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingUnitCompatibility

/-! # Tensor and unit compatibility of normalized reindexing

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- Normalized realization reindexing preserves the quotient-completion tensorator.
Source: Bhatt--Scholze, Remark 6.8.15; HRS Lemma 7.9; Stacks 07A4
(blueprint: lem-sf-adic-reindexing-tensor).

Proof: Represent both common-stage inputs at their compositum and choose the flat-term
K-flat models specified in their finite normalizations. Substitute the integral formula
for the comparison and the representative equations of finite normalization and tensor
reindexing. Both tensor routes take r tensor x tensor s tensor y to rs tensor
(x tensor y). The pure-section equations establish this on every homogeneous summand;
the signed total-tensor comparison makes it a cochain equality. The specified completion
comparison carries both quotient coaugmentations, including their zero shifted-product
coordinate, to the reindexed ones. Its scalar compatibility identifies these equalities
with the specified pullback tensor comparison. Descend by the K-flat representative
isomorphisms, raw rationalization, and common-stage inclusion. For the unit both routes
are scalar multiplication r tensor 1 maps to r. The unitor equation for the given
tensorator, or its tensor equation with the coefficient unit and cancellation of the
invertible tensorators, fixes the unit comparison. This proves the displayed unit
identity for the specified canonicalCommonStagePullbackTensor_unit witness. -/
theorem normalized_reindexing_tensor
    (C : FamilyCore l D)
    (h_integral_normalization : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
          (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g)) :
    (∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (M N : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) U.base.left),
    letI := (C.data T).units
    letI := (C.data U).units
    (derivedPull l T.base.left g.hom (C.ring T U g)).map ((C.data U).tensor.tensor.hom.app (M, N)) ≫
      (C.comparison T U g).inv.app ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj
        (M, N)) ≫
      (ordinary l T.base.left (C.data T).realization).map
        (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom M N).hom =
    (C.pullTensor T U g).tensor.hom.app
        ((ordinary l U.base.left (C.data U).realization).obj M,
         (ordinary l U.base.left (C.data U).realization).obj N) ≫
      (C.data T).tensor.closed.tensor.map (Prod.mkHom
        ((C.comparison T U g).inv.app M) ((C.comparison T U g).inv.app N)) ≫
      (C.data T).tensor.tensor.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
        (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N))
    ∧ (∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    letI := (C.data T).units
    letI := (C.data U).units
    (derivedPull l T.base.left g.hom (C.ring T U g)).map (C.data U).tensor.unit.hom ≫
      (C.comparison T U g).inv.app (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left) ≫
      (ordinary l T.base.left (C.data T).realization).map
        (C.unit_spec T U g).exists.choose.hom =
    (pullUnit l T.base.left g.hom (C.pullTensor T U g)).hom ≫ (C.data T).tensor.unit.hom) := by
  constructor
  · intro T U g M N
    exact normalized_reindexing_tensor_compatibility l D C T U g
      (h_integral_normalization T U g) M N
  · intro T U g
    exact normalized_reindexing_unit_compatibility l D C T U g
      (h_integral_normalization T U g)

end WeilConjectures.AdicQbarRealization
