/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Representative tensor square before cancellation

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9. The statement is the representative
calculation after postcomposition with the inverse of the target tensorator.
(blueprint: lem-sf-adic-reindexing-tensor-integral-cancelled).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/--
The normalized integral representative square, with the final realization
tensorator cancelled only after this equation is established.  This is the
finite K-flat, quotient-completion calculation in the proof of
`normalized_reindexing_tensor_integral`; the inverse tensorator is retained
explicitly so that the remaining theorem is a genuine cancellation step.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15, and
Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-reindexing-tensor-integral-cancelled).
-/
theorem normalized_reindexing_tensor_integral_cancelled
    (C : FamilyCore l D) (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h_integral_normalization :
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g)) :
    ∀ (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) U.base.left),
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := U.base.left) E
    let Q := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) U.base.left
    let M := I.obj (Q.obj K)
    let N := I.obj (Q.obj L)
    letI := (C.data T).units
    letI := (C.data U).units
    ((derivedPull l T.base.left g.hom (C.ring T U g)).map
        ((C.data U).tensor.tensor.hom.app (M, N)) ≫
      (C.comparison T U g).inv.app
        ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj (M, N)) ≫
      (ordinary l T.base.left (C.data T).realization).map
        (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom M N).hom) ≫
        (C.data T).tensor.tensor.inv.app
          ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
           (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N) =
    ((C.pullTensor T U g).tensor.hom.app
        ((ordinary l U.base.left (C.data U).realization).obj M,
         (ordinary l U.base.left (C.data U).realization).obj N) ≫
      (C.data T).tensor.closed.tensor.map (Prod.mkHom
        ((C.comparison T U g).inv.app M) ((C.comparison T U g).inv.app N)) ≫
      (C.data T).tensor.tensor.hom.app
        ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
         (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N) ≫
      (C.data T).tensor.tensor.inv.app
        ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
         (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N)) := by
  sorry

end WeilConjectures.AdicQbarRealization
