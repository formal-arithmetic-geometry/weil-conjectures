/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels

import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierTensorScalarSquare
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierTensorScalarTransport
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # The tensor-only scalar/completion square

Source: blueprint thm-coef-rational-verdier, paragraph 3, and
lem-coef-integral-finite-extension, evaluation and completion paragraphs.
(blueprint: lem-coef-rational-verdier-tensor-scalar-completion). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

attribute [local irreducible] HasDerivedCategory.standard
  integralCompletedTensor integralCompletedTensorComparison
  integralOperationsTensorComplexFunctor integralOrdinaryScalar
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  PurCompactSupport.scalarTensor PurCompactSupport.scalarTensorTotal
  scalarTensorOrdinary scalarTensorCompleted
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local implicit_reducible] Functor.mapHomologicalComplex
  completedOrdinaryScalarComplex coefficientTotalTensor IntegralFiniteExtension.tensorModel
  CategoryTheory.uniformProd CategoryTheory.prod' CategoryTheory.prod
  integralOperationsGoodComplex DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh HomotopyCategory.quotient
  constructibleIntegralTensor integralScalarExtensionOfUniverses
  sfConstructibleIntegralScalarExtension integralTensorScalarComparison
attribute [local instance 100000] PurCompactSupport.coefficientSiteSmall
  PurCompactSupport.coefficientRingSheafify PurCompactSupport.coefficientAbSheafify
  PurCompactSupport.coefficientAbLocallyBijective
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
private theorem inverse_cube {C : Type*} [Category C]
    {A B C' A' B' : C} (z : A ≅ B) (c : B ≅ C') (d : B' ≅ C')
    (e : A' ≅ B') (f : A ⟶ A')
    (h : z.hom ≫ c.hom = f ≫ e.hom ≫ d.hom) :
    c.inv ≫ z.inv ≫ f = d.inv ≫ e.inv := by
  have hf : f = z.hom ≫ c.hom ≫ d.inv ≫ e.inv := by
    rw [← Category.assoc z.hom c.hom, h]
    simp
  rw [hf]
  simp

private theorem inverse_cube_two {C : Type*} [Category* C]
    {A B B₁ C' A' B' : C} (z₁ : A ≅ B) (z₂ : B ≅ B₁) (c : B₁ ≅ C')
    (d : B' ≅ C') (e : A' ≅ B') (f : A ⟶ A')
    (h : (z₁ ≪≫ z₂).hom ≫ c.hom = f ≫ e.hom ≫ d.hom) :
    c.inv ≫ z₂.inv ≫ z₁.inv ≫ f = d.inv ≫ e.inv := by
  simpa only [Iso.trans_inv, Category.assoc] using inverse_cube (z₁ ≪≫ z₂) c d e f h

private theorem paste_three {C : Type*} [Category* C]
    {A B C₁ D E F G H : C}
    {a : A ⟶ B} {b : B ⟶ C₁} {c : A ⟶ D} {d : D ⟶ C₁}
    {e : B ⟶ E} {f : E ⟶ F} {g : C₁ ⟶ F} {h : D ⟶ G}
    {i : G ⟶ F} {j : A ⟶ H} {k : H ⟶ G}
    (h₁ : a ≫ b = c ≫ d) (h₂ : e ≫ f = b ≫ g)
    (h₃ : d ≫ g = h ≫ i) (h₄ : c ≫ h = j ≫ k) :
    (a ≫ e) ≫ f = j ≫ k ≫ i := by
  rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, h₃,
    ← Category.assoc, h₄, Category.assoc]

set_option maxHeartbeats 600000 in
-- The inverse comparison cube has several definitionally equivalent scalar-model endpoints.
set_option linter.unusedSectionVars false in
-- Preserve the original finite-type hypothesis in this public statement.
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- Scalar extension respects the normalized ordinary-to-completed tensor comparison.
This square contains no internal Hom, evaluation, dualizing object, or rationalization.

Source: blueprint thm-coef-rational-verdier.proof.md, paragraph 3; the normalized
completion calculation in lem-coef-integral-finite-extension.proof.md.
(blueprint: lem-coef-rational-verdier-tensor-scalar-completion).

Proof: represent K and M by flat-term K-flat complexes. The ordinary scalar tensorator
sends s tensor (x tensor y) to (s tensor x) tensor (1 tensor y). The representative
condition of each Completion identifies its map with the fixed completion chain map:
every positive quotient coordinate is the quotient tensor map and the shifted coordinate
is zero. The scalar completion map has the same quotient/zero-coordinate normalization.
Consequently completing before or after the ordinary scalar tensorator gives the same
map: on a homogeneous tensor both quotient coordinates are its scalar-extended quotient,
and both shifted coordinates vanish. Sheafification, the total-tensor coproduct
inclusions and the two mapping-fiber coordinates detect equality. Descend this equation
through the K-flat localization; representative independence and naturality transport it
to K and M. Invert the constructible tensor completion comparisons and the scalar
completion comparisons on K and M. The normalized definition of scalarTensorCompleted
then gives the displayed inverse square. Zero objects and the identity extension use
exactly the same quotient and zero-coordinate maps. -/
theorem tensor_scalar_completion
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (cE : Completion D l hl X E a) (cL : Completion D l hl X L b)
    (K M : sfIntegralConstructibleCategory l E X) :
    (@asIso _ _ _ _ (cL.map.app
      (((integralScalar l X E L i).obj K).obj, ((integralScalar l X E L i).obj M).obj))
      (cL.invertible ((integralScalar l X E L i).obj K)
        ((integralScalar l X E L i).obj M))).inv ≫
      b.tensor.map (Prod.mkHom
        (IntegralFiniteExtension.completion l E L i X K.obj K.property.1).inv
        (IntegralFiniteExtension.completion l E L i X M.obj M.property.1).inv) ≫
      (PurCompactSupport.scalarTensor (completedCoefficientMap l E L i X)
        (IntegralFiniteExtension.tensorModel X a)
        (IntegralFiniteExtension.tensorModel X b)).inv.app (K.obj, M.obj) ≫
      (completedScalarComparison l E L i X).app (a.tensor.obj (K.obj, M.obj)) =
    (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X) K M).inv.hom ≫
      (integralScalarExtensionOfUniverses l E L i X).map
        (@asIso _ _ _ _ (cE.map.app (K.obj, M.obj)) (cE.invertible K M)).inv := by
  let := units D l hl X
  let F := pbcDerivedExtend (completedCoefficientMap l E L i X)
  let T := integralScalarExtensionOfUniverses l E L i X
  let χ := completedScalarComparison l E L i X
  let TK := (integralScalar l X E L i).obj K
  let TM := (integralScalar l X E L i).obj M
  let A := (constructibleIntegralTensor l E X).obj (K, M)
  let uK := IntegralFiniteExtension.completion l E L i X K.obj K.property.1
  let uM := IntegralFiniteExtension.completion l E L i X M.obj M.property.1
  let uA := IntegralFiniteExtension.completion l E L i X A.obj A.property.1
  let c := @asIso _ _ _ _ (cL.map.app (TK.obj, TM.obj)) (cL.invertible TK TM)
  let c₀ := @asIso _ _ _ _ (cE.map.app (K.obj, M.obj)) (cE.invertible K M)
  let μ := PurCompactSupport.scalarTensor (completedCoefficientMap l E L i X)
    (IntegralFiniteExtension.tensorModel X a) (IntegralFiniteExtension.tensorModel X b)
  obtain ⟨t, e, ht, he, hχ⟩ := integralScalarOrdinaryModelComparison l E L i X
  change integralOrdinaryDerivedScalar l E L i X ≅ F at e
  change e.hom ≫ χ = scalarCompletion l E L i X at hχ
  let γ := Functor.isoWhiskerLeft (integralCompletedTensor l E X) e.symm ≪≫
    scalarTensorOrdinary l E L i X ≪≫
    Functor.isoWhiskerRight (NatIso.prod e e) (integralCompletedTensor l L X)
  let θ := scalarTensorCompleted l E L i X K.obj M.obj K.property.1 M.property.1 A.property.1
  have hθ := tensor_scalar_completion_transport l E L i X e hχ K.obj M.obj
    K.property.1 M.property.1 A.property.1
  change γ.hom.app (K.obj, M.obj) ≫
      (integralCompletedTensor l L X).map (Prod.mkHom uK.hom uM.hom) =
    uA.hom ≫ θ.hom at hθ
  have hsquare := NatTrans.congr_app
    (tensor_completion_scalar_square D l hl X E L i a b cE cL t e ht he) (K.obj, M.obj)
  change μ.hom.app (K.obj, M.obj) ≫ cL.map.app (F.obj K.obj, F.obj M.obj) =
    F.map c₀.hom ≫ γ.hom.app (K.obj, M.obj) at hsquare
  have hn := cL.map.naturality (Prod.mkHom uK.hom uM.hom)
  change b.tensor.map (Prod.mkHom uK.hom uM.hom) ≫ c.hom =
    cL.map.app (F.obj K.obj, F.obj M.obj) ≫
      (integralCompletedTensor l L X).map (Prod.mkHom uK.hom uM.hom) at hn
  let z := μ.app (K.obj, M.obj) ≪≫ b.tensor.mapIso (Iso.prod uK uM)
  have hz : z.hom ≫ c.hom =
      χ.app (a.tensor.obj (K.obj, M.obj)) ≫ (T.mapIso c₀).hom ≫ θ.hom := by
    change (μ.hom.app (K.obj, M.obj) ≫ b.tensor.map (Prod.mkHom uK.hom uM.hom)) ≫
      c.hom = _
    have hnat := χ.naturality c₀.hom
    change F.map c₀.hom ≫ uA.hom = χ.app _ ≫ T.map c₀.hom at hnat
    exact paste_three hsquare hn hθ hnat
  change c.inv ≫ b.tensor.map (Prod.mkHom uK.inv uM.inv) ≫
    μ.inv.app (K.obj, M.obj) ≫ χ.app (a.tensor.obj (K.obj, M.obj)) = θ.inv ≫ T.map c₀.inv
  exact inverse_cube_two (μ.app (K.obj, M.obj))
    (b.tensor.mapIso (Iso.prod uK uM)) c θ (T.mapIso c₀)
    (χ.app (a.tensor.obj (K.obj, M.obj))) hz

end WeilConjectures.RationalVerdier
