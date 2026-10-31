/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Rational.RationalVerdier
public import WeilConjectures.SixFunctors.Completed.CompletedTensorHomTranspose
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex

import all WeilConjectures.SixFunctors.Completed.CompletedTensorHomTranspose
import WeilConjectures.SmoothPurity.Integral.IntegralBraidingScalarExtensionSquare
import WeilConjectures.SixFunctors.Scalar.ScalarHomPresentationEvaluation
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompletion
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierTensorScalarCompletion
import all WeilConjectures.SixFunctors.RationalOperations.RationalHomScalarCounitNormalization
import all WeilConjectures.SixFunctors.Coef.CoefIntegralFiniteExtension
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality

/-! # Integral scalar extension and normalized Hom evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] WeilConjectures.rationalDerivedTensor
  WeilConjectures.rationalDerivedInternalHom WeilConjectures.podRationalClosed
  WeilConjectures.rationalHomScalarComparison

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  RationalVerdier.units

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem scalarHom_presentations
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) :
    ∃ (a : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (b : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l F X)),
      ∀ P : (constructibleIntegralHomPairs l E X).FullSubcategory,
        IntegralFiniteExtension.v l E F ι X a b P.obj.1.unop.obj P.obj.2.obj
          P.obj.1.unop.property.1 P.obj.2.property.1 =
            (integralHomScalarComparison l E F ι X P).hom.hom := by
  obtain ⟨a, b, e, he, hc⟩ := scalarHom_presentation_evaluation l E X F ι
  refine ⟨a, b, ?_⟩
  intro P
  have ec (N : DerivedCategory (scalarReductionSource l E X))
      (hN : IsSfDerivedComplete l E X N) :
      IntegralFiniteExtension.completion l E F ι X N hN =
        e.app N ≪≫ scalarCompletionIso l E F ι X N hN := by
    apply Iso.ext
    exact hc N
  change IntegralFiniteExtension.v l E F ι X a b _ _ _ _ =
    (scalarHomCompleted l E F ι X _ _ _ _ _).hom
  unfold IntegralFiniteExtension.v scalarHomCompleted
  rw [ec, ec, ec]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.op_hom, Category.assoc]
  have hprod : Prod.mkHom
      (((scalarCompletionIso l E F ι X P.obj.1.unop.obj
        P.obj.1.unop.property.1).inv ≫ e.inv.app P.obj.1.unop.obj).op)
      (e.hom.app P.obj.2.obj ≫
        (scalarCompletionIso l E F ι X P.obj.2.obj P.obj.2.property.1).hom) =
      Prod.mkHom (e.inv.app P.obj.1.unop.obj).op (e.hom.app P.obj.2.obj) ≫
        Prod.mkHom
          ((scalarCompletionIso l E F ι X P.obj.1.unop.obj
            P.obj.1.unop.property.1).inv.op)
          (scalarCompletionIso l E F ι X P.obj.2.obj P.obj.2.property.1).hom := by
    ext <;> simp
  erw [hprod, Functor.map_comp, reassoc_of% he P.obj.1.unop.obj P.obj.2.obj]
  simp only [Iso.app_inv, asIso_hom]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

private theorem integralScalar_argumentEvaluation
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F)
    (P : (constructibleIntegralHomPairs l E X).FullSubcategory) :
    letI := RationalVerdier.units D l hl X
    let S := RationalVerdier.integralScalar l X E F ι
    let H := (constructibleIntegralHom l E X).obj P
    let PF := integralHomScalarPair l E F ι X P
    (constructibleIntegralTensor l F X).map
        (Prod.mkHom (𝟙 (S.obj P.obj.1.unop))
          (integralHomScalarComparison l E F ι X P).hom) ≫
      (pullbackTensorIntegralBraiding l F X (S.obj P.obj.1.unop)
        ((constructibleIntegralHom l F X).obj PF)).hom ≫
      (podIntegralClosed l F X).evaluation PF =
    (integralTensorScalarComparison l E F ι X P.obj.1.unop H).inv ≫
      S.map ((pullbackTensorIntegralBraiding l E X P.obj.1.unop H).hom ≫
        (podIntegralClosed l E X).evaluation P) := by
  let := RationalVerdier.units D l hl X
  dsimp only
  obtain ⟨a, b, hv⟩ := scalarHom_presentations l X E F ι
  obtain ⟨cE⟩ := RationalVerdier.completion_exists D l hl X E a
  obtain ⟨cF⟩ := RationalVerdier.completion_exists D l hl X F b
  apply ObjectProperty.hom_ext
  let S := integralScalarExtensionOfUniverses l E F ι X
  let G := pbcDerivedExtend (completedCoefficientMap l E F ι X)
  let K := P.obj.1.unop
  let H := (constructibleIntegralHom l E X).obj P
  let PF := integralHomScalarPair l E F ι X P
  let HK := (constructibleIntegralHom l F X).obj PF
  let v := (integralHomScalarComparison l E F ι X P).hom.hom
  let c (U V : sfIntegralConstructibleCategory l F X) :=
    @asIso _ _ _ _ (cF.map.app (U.obj, V.obj)) (cF.invertible U V)
  let TK := (RationalVerdier.integralScalar l X E F ι).obj K
  let TH := (RationalVerdier.integralScalar l X E F ι).obj H
  have hci : (integralCompletedTensor l F X).map (Prod.mkHom (𝟙 TK.obj) v) ≫
      (c TK HK).inv = (c TK TH).inv ≫ b.tensor.map (Prod.mkHom (𝟙 TK.obj) v) := by
    apply (cancel_epi (c TK TH).hom).1
    have hn := cF.map.naturality (Prod.mkHom (𝟙 TK.obj) v)
    change b.tensor.map (Prod.mkHom (𝟙 TK.obj) v) ≫ (c TK HK).hom =
      (c TK TH).hom ≫ (integralCompletedTensor l F X).map
        (Prod.mkHom (𝟙 TK.obj) v) at hn
    rw [← Category.assoc, ← hn]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have he := IntegralFiniteExtension.v_evaluation l E F ι X a b
    (IntegralHom.evaluation_naturality X _ b)
    K.obj P.obj.2.obj K.property.1 P.obj.2.property.1
  rw [hv P] at he
  have hn := (completedScalarComparison l E F ι X).naturality
    ((a.adjunction K.obj).counit.app P.obj.2.obj)
  have hs := RationalVerdier.tensor_scalar_completion D l hl X E F ι a b cE cF K H
  have eE := RationalOperations.integralCounit_normalized D l hl X E a cE P
  have eF := RationalOperations.integralCounit_normalized D l hl X F b cF PF
  change (pullbackTensorIntegralBraiding l F X TK HK).hom.hom ≫
      ((podIntegralClosed l F X).evaluation PF).hom =
        (c TK HK).inv ≫ (b.adjunction TK.obj).counit.app PF.obj.2.obj at eF
  change (integralCompletedTensor l F X).map (Prod.mkHom (𝟙 TK.obj) v) ≫
      (pullbackTensorIntegralBraiding l F X TK HK).hom.hom ≫
        ((podIntegralClosed l F X).evaluation PF).hom = _
  rw [eF, ← Category.assoc, hci, Category.assoc]
  erw [he]
  change (c TK TH).inv ≫
      (b.tensor.map _ ≫ _ ≫ G.map ((a.adjunction K.obj).counit.app P.obj.2.obj) ≫
        (completedScalarComparison l E F ι X).app P.obj.2.obj) = _
  change G.map _ ≫ (completedScalarComparison l E F ι X).app P.obj.2.obj =
    (completedScalarComparison l E F ι X).app (a.tensor.obj (K.obj, H.obj)) ≫
      S.map ((a.adjunction K.obj).counit.app P.obj.2.obj) at hn
  rw [hn]
  have hs' := congrArg
    (fun z ↦ z ≫ S.map ((a.adjunction K.obj).counit.app P.obj.2.obj)) hs
  simp only [Category.assoc] at hs'
  erw [hs']
  erw [← S.map_comp, ← eE]
  rfl

/-- Scalar extension preserves the completed integral Hom-first evaluation.
Source: the finite coefficient comparison in the proof of rational Verdier duality
(blueprint: lem-coef-integral-hom-scalar-evaluation).

Proof: choose normalized ordinary tensor presentations inside the proof. Their
specified scalar Hom and completion equations identify the ordinary evaluation
transpose, conjugated by completion, with the integral Hom scalar comparison.
Normalize both completed counits using the ordinary/completed adjoint square.
Move the Hom comparison past inverse tensor completion by naturality, apply the
ordinary evaluation identity, and use scalar-completion naturality and the tensor
scalar-completion square. This proves the argument-first evaluation equation.
Naturality of braiding and the integral scalar braiding square convert it to
Hom-first evaluation by cancelling the source braiding. All choices occur only
inside a proof; no object is constructed from a mere existential witness. -/
theorem rationalHomScalar_integralEvaluation
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F)
    (P : (constructibleIntegralHomPairs l E X).FullSubcategory) :
    letI := RationalVerdier.units D l hl X
    let S := RationalVerdier.integralScalar l X E F ι
    let H := (constructibleIntegralHom l E X).obj P
    let PF := integralHomScalarPair l E F ι X P
    (constructibleIntegralTensor l F X).map
        (Prod.mkHom (integralHomScalarComparison l E F ι X P).hom
          (𝟙 (S.obj P.obj.1.unop))) ≫
      (podIntegralClosed l F X).evaluation PF =
    (integralTensorScalarComparison l E F ι X H P.obj.1.unop).inv ≫
      S.map ((podIntegralClosed l E X).evaluation P) := by
  let := RationalVerdier.units D l hl X
  dsimp only
  let S := RationalVerdier.integralScalar l X E F ι
  let K := P.obj.1.unop
  let H := (constructibleIntegralHom l E X).obj P
  let v := (integralHomScalarComparison l E F ι X P).hom
  have hb := integralBraidingScalarExtensionSquare l E F ι X K H
  have hi : (pullbackTensorIntegralBraiding l F X (S.obj K) (S.obj H)).hom ≫
      (integralTensorScalarComparison l E F ι X H K).inv =
    (integralTensorScalarComparison l E F ι X K H).inv ≫
      S.map (pullbackTensorIntegralBraiding l E X K H).hom := by
    apply (cancel_epi (integralTensorScalarComparison l E F ι X K H).hom).1
    rw [← Category.assoc, ← hb]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
    rfl
  apply (cancel_epi (pullbackTensorIntegralBraiding l F X (S.obj K) (S.obj H)).hom).1
  rw [← Category.assoc, ← integralBraiding_naturality l F X
    (S.obj K) (S.obj K) (S.obj H) _ (𝟙 _) v]
  rw [Category.assoc, integralScalar_argumentEvaluation D l hl X E F ι P,
    ← Category.assoc, hi, Category.assoc, ← S.map_comp]

end WeilConjectures
