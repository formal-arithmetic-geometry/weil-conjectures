/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.CanonicalCoefficientPullbackModels
import all Sheaf.Paper.CanonicalCoefficientPullbackModels
import all Sheaf.Paper.ConstantWeilStructure

/-!
# The unit and Roos augmentation for canonical coefficient pullback

Source: Stacks Tags 03D6 and 08TC; the regular-unit and Roos APIs in
`Sheaf.Paper.ConstantWeilStructure`.
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).

This module contains proved comparison results and private helpers for the coefficient comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] regularExtensionIso regularExtensionPresheafIso
  identityRestrictionIso scalarReductionExistence HasDerivedCategory.standard
  unrestrictedIntegralReductionExistence limit finiteRegularIso finiteSingleRegularIso
  finitePullbackRegularIso pullbackLevelRegularIso pullbackUnitLevel chainUnitCandidate
  integralDerivedPullback integralDerivedPullbackComparison
  constantWeilIntegralRoosComparison
  constantWeilIntegralLambda constantWeilDerivedCoefficientComparison
  SheafOfModules.monoidalCategory constantSheaf
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] canonicalCoefficientIntegralComparison
  canonicalCoefficientInverseImageTransport
  canonicalCoefficientLambda canonicalCoefficientKappa canonicalCoefficientLambdaFinite
  canonicalCoefficientFiniteComparison canonicalCoefficientPullbackReductionIso
  canonicalCoefficientRho canonicalCoefficientProjection canonicalCoefficientInverseProjection
  canonicalCoefficientTheta canonicalCoefficientPullbackTransition canonicalCoefficientTransition
  canonicalCoefficientInverseTransition

attribute [local irreducible] canonicalCoefficientIntegralUnit
  canonicalCoefficientFiniteUnit canonicalCoefficientFiniteKappaComplex
  coefficientFiniteInverseIso coefficientFinitePullIso

/-- The chain coefficient identification from inverse image of the regular complex to R_X[0].
It uses the exact single-complex comparison and the inverse of the actual coefficient unit.
Source: Stacks 03D6; normalized regular-module inverse image
(blueprint: lem-pod-canonical-coefficient-unit-roos-normalization). -/
def coefficientIntegralInverseIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj
      (constantWeilIntegralComplex l E Y) ≅ constantWeilIntegralComplex l E X :=
  (HomologicalComplex.singleMapHomologicalComplex
      (inverseImageIntegralModules l E g) (.up ℤ) 0).app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso
      (@asIso _ _ _ _ (canonicalCoefficientIntegralUnit l E g)
        (canonicalCoefficientModelMaps_isIso l E g).1).symm

attribute [local irreducible] coefficientIntegralInverseIso

private theorem coefficientTheta_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    canonicalCoefficientTheta l E g = constantWeilIntegralTheta l E g := by
  apply Iso.ext
  simp only [canonicalCoefficientTheta, canonicalCoefficientLambda,
    canonicalCoefficientInverseImageTransport, constantWeilIntegralTheta,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem coefficientReductionComplex_eq (W : Scheme.{u}) (n : ℕ) :
    canonicalCoefficientReductionComplex l E W n = (finiteSingleRegularIso l E W n).hom := by
  unfold canonicalCoefficientReductionComplex finiteSingleRegularIso
  rw [coefficientReduction_eq]
  rfl

private theorem coefficientInverseUnit_one {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (U : X.ProEt) :
    (((coefficientIntegralInverseIso l E g).inv.f 0).val.app (op U))
      (constantWeilUnitSection l E X U) =
    constantWeilUnitSection l E Y ((proEtaleIsoPostcompose g).obj U) := by
  let sX := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X))
  let sY := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))
  have h : sX.inv ≫ (coefficientIntegralInverseIso l E g).inv.f 0 =
      canonicalCoefficientIntegralUnit l E g ≫
        (inverseImageIntegralModules l E g).map sY.inv := by
    simp only [coefficientIntegralInverseIso, Iso.trans_inv,
      HomologicalComplex.comp_f, Functor.mapIso_inv, Iso.symm_inv, asIso_hom,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, Iso.app_inv,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      Category.assoc, Iso.inv_hom_id_assoc, sX, sY]
  change ((sX.inv ≫ (coefficientIntegralInverseIso l E g).inv.f 0).val.app (op U))
    (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj (op U)) = _
  rw [h]
  unfold canonicalCoefficientIntegralUnit
  change sY.inv.val.app _
    ((inv (inverseImageCompletedCoefficientMap l E g)).hom.app (op U) 1 * 1) = _
  simp only [map_one, one_mul]
  rfl

private theorem coefficientUnit_theta {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) :
    (coefficientIntegralInverseIso l E g).inv ≫
      inverseImageReductionTheta l E g n (constantWeilIntegralComplex l E Y) =
    pullbackUnitLevel l E g n := by
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  apply regular_hom_ext l E X ((proEtaleBaseChange g).obj T)
    (hT.isTerminalObj (proEtaleBaseChange g) T)
  let U := (proEtaleBaseChange g).obj T
  let V := (proEtaleIsoPostcompose g).obj U
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [coefficientInverseUnit_one]
  unfold inverseImageReductionTheta
  erw [(inverseImageReductionTheta_existsUnique l E g n
    (constantWeilIntegralComplex l E Y)).exists.choose_spec 0 U]
  have hx : unrestrictedIntegralTensorSection l E Y n
      ((constantWeilIntegralComplex l E Y).X 0) (op V) 1
      (constantWeilUnitSection l E Y V) = constantWeilReducedUnitSection l E Y n V := by
    unfold constantWeilReducedUnitSection constantWeilUnitSection
    rw [reduction_map_tensor]
    rfl
  rw [hx]
  rw [← pullbackUnitSections_base]
  have hn := (pullbackUnitSections l E g n).property (proEtaleIsoCommaArrow g U).op
  change (((constantWeilPullbackTower l E g).obj (op n)).X 0).val.map
    (proEtaleIsoCommaArrow g U).op _ = _
  erw [hn]
  rw [pullbackUnitSections_base]
  exact (pullbackUnitLevel_generator l E g n T).symm

/-- Conjugating the specified zero-homotopy augmentation by the regular coefficient
identification gives the normalized strict Roos chain unit.
Source: Stacks 03D6 and 08TC; coefficient comparison, augmentation step
(blueprint: lem-pod-canonical-coefficient-unit-roos-normalization).
Proof: each actual product projection agrees by regular-unit extensionality and the
specified reduction-theta formula. Both shifted cone coordinates vanish, so the
mapping-cocone extensionality lemma identifies the maps. -/
theorem coefficientUnit_roos {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (coefficientIntegralInverseIso l E g).inv ≫
      inverseImageRoosComparisonComplex l E g (constantWeilIntegralComplex l E Y) =
    constantWeilChainUnit l E g := by
  have he : constantWeilChainUnit l E g = chainUnitCandidate l E g :=
    normalized_chainUnit_unique l E g _
      (constantWeilChainUnit_existsUnique l E g).exists.choose_spec
  rw [he]
  unfold inverseImageRoosComparisonComplex
  change (coefficientIntegralInverseIso l E g).inv ≫
    CochainComplex.mappingCocone.lift (constantWeilPullbackRoosEndomorphism l E g)
      (inverseImageReductionProduct l E g (constantWeilIntegralComplex l E Y)) 0 _ = _
  apply cocone_hom_ext (constantWeilPullbackRoosEndomorphism l E g)
  · simp only [chainUnitCandidate,
      Category.assoc, CochainComplex.mappingCocone.lift_fst]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, inverseImageReductionProduct, pullbackUnitProduct, Pi.lift_π]
    erw [Pi.lift_π]
    exact coefficientUnit_theta l E g n
  · intro i
    simp only [HomologicalComplex.comp_f, Category.assoc,
      chainUnitCandidate,
      CochainComplex.mappingCocone.lift_f_snd_v,
      CochainComplex.HomComplex.Cochain.zero_v, comp_zero]

end WeilConjectures
