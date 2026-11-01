/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData

import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingTensorIntegralCancelled

/-! # Tensor square on integral objects at one finite coefficient field

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9. The normalization calculation below is an
agent-written refinement of these comparison results.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- The normalized tensor square on two integral objects over one fixed coefficient field.
Source: Bhatt--Scholze, Proposition 6.8.14, Remark 6.8.15 and Lemma 6.5.5;
Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-reindexing-tensor-integral).

Proof: Choose flat-term K-flat representatives of K and L in the integral category.
Expand integralRealizationAgreement at K, L and their completed tensor. Expand the
finite integral_tensor equations at source and target, and the finite representative
and reindexing representative equations on these K-flat models. The remaining square
is the base-change square for the total tensor and its quotient-completion comparison.
On a homogeneous generator with scalar factors s and t, finiteBalanceSections and
reindexTensorPure send both routes to the same total-tensor generator with factor s*t;
RingReindex.functions identifies the coefficient factors. The ordinary cochain pullback
comparison respects the signed differential and each quotient transition, so balancing
extends this to equality of chain maps. For the full mapping-fiber completion map, its
product coordinate is the prescribed quotient map and its shifted coordinate is zero;
both are preserved by the base-change comparison. Thus the whole completion square
commutes, not merely its reductions. Apply the representative isomorphisms and invert
the completion comparison on constructible tensors. Raw rationalization and inclusion
at E preserve this equality. The defining representative equations for the canonical
rational and common-stage pullback tensor comparisons identify the resulting arrow
with the displayed canonical map. Cancel the adjacent representative comparisons.
This proves the square at E using only the integral normalization at E; no extension
of coefficients, arbitrary common-stage object, or transport to such an object is used.
-/
theorem normalized_reindexing_tensor_integral
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
        (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N) := by
  intro K L
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := U.base.left) E
  let Q := sfRationalConstructibleLocalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) U.base.left
  let M := I.obj (Q.obj K)
  let N := I.obj (Q.obj L)
  letI := (C.data T).units
  letI := (C.data U).units
  apply (cancel_mono ((C.data T).tensor.tensor.inv.app
    ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
     (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N))).mp
  dsimp only [M, N, I, Q]
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using
    normalized_reindexing_tensor_integral_cancelled l D C T U g E
    h_integral_normalization K L

end WeilConjectures.AdicQbarRealization
