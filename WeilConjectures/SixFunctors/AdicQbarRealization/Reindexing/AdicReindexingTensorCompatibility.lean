/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData

import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingTensorIntegral
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso

/-! # Tensor compatibility of a normalized realization comparison

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9. The normalization calculation below is an
agent-written refinement of these comparison results.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem

universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

private theorem app_eq_of_iso {A B : Type*} [Category* A] [Category* B]
    {F G : A ⥤ B} (α β : F ⟶ G) {X Y : A} (e : X ≅ Y)
    (h : α.app Y = β.app Y) : α.app X = β.app X := by
  apply (cancel_mono (G.map e.hom)).mp
  rw [← α.naturality, ← β.naturality, h]

/-- The tensor equation for one fixed scheme-isomorphism comparison.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-reindexing-tensor-compatibility).

Proof: Form the two routes as natural transformations of bifunctors, using the
natural isomorphism whose components are canonicalCommonStagePullbackTensor.
Choose the compositum E of the coefficient fields of M and N. The specified
isoToStage maps identify both with objects included from E. Raw rationalization
introduces no new objects, so each such object is the rationalization of its
underlying integral object. Apply normalized_reindexing_tensor_integral at E,
using the normalization hypothesis only at that field. Naturality transports the
equality of components back along the product of the two isoToStage maps;
postcomposition with the image of this isomorphism cancels. The component
specification for the canonical comparison gives exactly the displayed equation.
No identity, composition or internal-Hom equation is used. -/
theorem normalized_reindexing_tensor_compatibility
    (C : FamilyCore l D) (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (h_integral_normalization : ∀ (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g)) :
    ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) U.base.left),
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
  let := (C.data T).units
  let := (C.data U).units
  let P := commonStageDerivedPullback l (PadicAlgCl l) g.hom
  let JX := ordinary l T.base.left (C.data T).realization
  let JY := ordinary l U.base.left (C.data U).realization
  let G := derivedPull l T.base.left g.hom (C.ring T U g)
  let TY := commonStageDerivedTensor l (PadicAlgCl l) U.base.left
  let BX := (C.data T).tensor.closed.tensor
  let a := C.comparison T U g
  intro M N
  obtain ⟨_, _, _, _, _, _, _, ⟨μ, hμ⟩, _⟩ :=
    derivedPullbackTensorIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) M.stage)
      g.hom 0 (PadicAlgCl l)
  let left := whiskerRight (C.data U).tensor.tensor.hom G ≫
    whiskerLeft TY a.inv ≫ whiskerRight μ.hom JX
  let right := whiskerLeft (JY.prod JY) (C.pullTensor T U g).tensor.hom ≫
    whiskerRight (NatTrans.prod a.inv a.inv) BX ≫
    whiskerLeft (P.prod P) (C.data T).tensor.tensor.hom
  let E := Padic.finiteCoefficientCompositum l (PadicAlgCl l) M.stage N.stage
  obtain ⟨hM, hN⟩ := (Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1
    M.stage N.stage
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) U.base.left
  let eM := S.isoToStage M hM
  let eN := S.isoToStage N hN
  have hStage (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (K L : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) F) U.base.left) :
      let I := GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := U.base.left) F
      left.app (I.obj K, I.obj L) = right.app (I.obj K, I.obj L) := by
    rcases K with ⟨K⟩
    rcases L with ⟨L⟩
    have hi := normalized_reindexing_tensor_integral l D C T U g F
      (h_integral_normalization F) K L
    simpa only [left, right, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      NatTrans.prod, Functor.prod_obj, G, JX, JY, P, TY, BX, a,
      sfRationalConstructibleLocalization, ScalarLocalization.localization,
      ← Iso.app_hom, hμ] using hi
  have h : left.app (M, N) = right.app (M, N) := by
    apply app_eq_of_iso left right (eM.prod eN)
    exact hStage E (M.toStage hM) (N.toStage hN)
  simpa only [left, right, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    NatTrans.prod, Functor.prod_obj, G, JX, JY, P, TY, BX, a,
    ← Iso.app_hom, hμ] using h

end WeilConjectures.AdicQbarRealization
