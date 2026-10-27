/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.CanonicalCoefficientPullbackModels
import all Sheaf.Paper.CanonicalCoefficientPullbackModels
import all Sheaf.Paper.CanonicalCoefficientUnitNormalization
import all Sheaf.Paper.ConstantWeilStructure

/-!
# Normalization of the canonical regular coefficient chain maps

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


attribute [local irreducible] coefficientIntegralInverseIso

private theorem coefficientFiniteComparison_eq {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    canonicalCoefficientFiniteComparison l E g n = coefficientFiniteInverseIso l E g n := by
  unfold canonicalCoefficientFiniteComparison coefficientFiniteInverseIso
  rfl

private theorem coefficientFiniteCollapse {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    (canonicalCoefficientLambdaFinite l E g n).hom ≫
      (canonicalCoefficientFiniteComparison l E g n).hom =
    (coefficientFinitePullIso l E g n).hom := by
  have := canonicalCoefficientFiniteKappa_isIso l E g n
  apply (cancel_epi (canonicalCoefficientFiniteKappaComplex l E g n)).1
  simp only [canonicalCoefficientLambdaFinite, Iso.symm_hom, asIso_inv,
    IsIso.hom_inv_id_assoc, coefficientFiniteComparison_eq]
  rw [coefficientFiniteKappa_formula]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def coefficientProjectionComplex (W : Scheme.{u}) (n : ℕ) :=
  (CochainComplex.singleFunctor _ 0).map (constantCoefficientProjection l E W n) ≫
    ((scalarReductionRestriction l E W n).mapCochainComplexSingleFunctor 0).inv.app
      (SheafOfModules.unit (integralCoefficientSheaf l E W n))

attribute [local irreducible] coefficientProjectionComplex

private theorem coefficientUnit_projection {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    pullbackUnitLevel l E g n ≫ (canonicalCoefficientPullbackReductionIso l E g n).hom ≫
      (canonicalCoefficientRes l E X n).map (coefficientFinitePullIso l E g n).hom =
    coefficientProjectionComplex l E X n := by
  apply (cancel_mono
    (((scalarReductionRestriction l E X n).mapCochainComplexSingleFunctor 0).hom.app
      (SheafOfModules.unit (integralCoefficientSheaf l E X n)))).1
  simp only [coefficientProjectionComplex, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  have h := pullbackLevelRegularIso_projection l E g n
  simpa only [pullbackLevelRegularIso, canonicalCoefficientPullbackReductionIso,
    coefficientReductionComplex_eq, coefficientFinitePullIso, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, Functor.map_comp, Category.assoc] using! h

private theorem coefficientChainUnit_projection {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    constantWeilChainUnit l E g ≫
      CochainComplex.mappingCocone.fst (constantWeilPullbackRoosEndomorphism l E g) ≫
      Pi.π (fun m ↦ (constantWeilPullbackTower l E g).obj (op m)) n =
    pullbackUnitLevel l E g n := by
  have he : constantWeilChainUnit l E g = chainUnitCandidate l E g :=
    normalized_chainUnit_unique l E g _
      (constantWeilChainUnit_existsUnique l E g).exists.choose_spec
  rw [he]
  simp only [chainUnitCandidate, CochainComplex.mappingCocone.lift_fst_assoc,
    pullbackUnitProduct, Pi.lift_π]

private theorem coefficientRho_unit {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    (constantWeilIntegralRoosComparison l E g).inv ≫ canonicalCoefficientRho l E g n =
      DerivedCategory.Q.map (pullbackUnitLevel l E g n ≫
        (canonicalCoefficientPullbackReductionIso l E g n).hom) := by
  simp only [constantWeilIntegralRoosComparison, canonicalCoefficientRho,
    Iso.trans_inv, Iso.symm_inv, asIso_hom, Iso.app_inv,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  rw [← Category.assoc, coefficientChainUnit_projection]

private theorem coefficientTheta_projection {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    (canonicalCoefficientTheta l E g).hom ≫ canonicalCoefficientProjection l E X n =
      canonicalCoefficientRho l E g n ≫ DerivedCategory.Q.map
        ((canonicalCoefficientRes l E X n).map
          ((canonicalCoefficientLambdaFinite l E g n).hom ≫
            (canonicalCoefficientFiniteComparison l E g n).hom)) := by
  rw [coefficientTheta_eq, coefficientFiniteCollapse]
  simp only [constantWeilIntegralTheta, constantWeilIntegralLambda, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (constantWeilIntegralRoosComparison l E g).inv).1
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, coefficientRho_unit, ← DerivedCategory.Q.map_comp,
    Category.assoc, coefficientUnit_projection]
  unfold canonicalCoefficientProjection coefficientProjectionComplex
  rfl

private theorem coefficientRho_compatible {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    canonicalCoefficientRho l E g (n + 1) ≫
      DerivedCategory.Q.map (canonicalCoefficientPullbackTransition l E g n) =
    canonicalCoefficientRho l E g n := by
  apply (cancel_epi (constantWeilIntegralRoosComparison l E g).inv).1
  rw [← Category.assoc, coefficientRho_unit, coefficientRho_unit,
    ← DerivedCategory.Q.map_comp]
  congr 1
  simp only [canonicalCoefficientPullbackTransition, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc, pullbackUnitLevel_transition]

private theorem coefficientIntegralComparison_factor {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    (canonicalCoefficientIntegralComparison l E g).hom =
      (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app
          (constantWeilIntegralComplex l E Y) ≫
        DerivedCategory.Q.map (coefficientIntegralInverseIso l E g).hom := by
  apply (cancel_epi ((inverseImageIntegralModules l E g).mapDerivedCategoryFactors.inv.app
    (constantWeilIntegralComplex l E Y))).1
  let e := (@asIso _ _ _ _ (canonicalCoefficientIntegralUnit l E g)
    (canonicalCoefficientModelMaps_isIso l E g).1).symm
  let F := inverseImageIntegralModules l E g
  have h := F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))
  have h' := congrArg (fun f ↦ f ≫
    (DerivedCategory.singleFunctor (integralTowerModules l E X) 0).map e.hom) h
  simpa only [canonicalCoefficientIntegralComparison, coefficientIntegralInverseIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc, e] using! h'

private theorem coefficientLambda_factor {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    canonicalCoefficientLambda l E g = constantWeilIntegralRoosComparison l E g ≪≫
      (canonicalCoefficientIntegralComparison l E g).symm := by
  apply Iso.ext
  simp only [canonicalCoefficientLambda, canonicalCoefficientInverseImageTransport,
    constantWeilIntegralLambda, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- The specified kappa factors through the actual regular coefficient comparison and
inverse normalized Roos comparison.
Source: Stacks 03D6 and 08TC; coefficient comparison, identity-resolution step
(blueprint: lem-pod-canonical-coefficient-chain-normalization).
Proof: use the conjugated augmentation equation, apply localization, and identify the
single-complex comparison with the exact derived comparison. Both resolution maps
are identities, leaving precisely this composite. -/
theorem coefficientKappa_factor {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    canonicalCoefficientKappa l E g hX hY =
      (canonicalCoefficientIntegralComparison l E g).hom ≫
        (constantWeilIntegralRoosComparison l E g).inv := by
  have hr : inverseImageRoosComparisonComplex l E g (constantWeilIntegralComplex l E Y) =
      (coefficientIntegralInverseIso l E g).hom ≫ constantWeilChainUnit l E g := by
    apply (cancel_epi (coefficientIntegralInverseIso l E g).inv).1
    simpa only [Iso.inv_hom_id_assoc] using coefficientUnit_roos l E g
  simp only [canonicalCoefficientKappa, inverseImagePullbackComparison,
    CategoryTheory.Functor.map_id, IsIso.inv_id]
  erw [hr]
  rw [Functor.map_comp]
  simp only [coefficientIntegralComparison_factor, constantWeilIntegralRoosComparison,
    Iso.trans_inv, Iso.symm_inv, asIso_hom, Iso.app_inv, Category.assoc]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

end WeilConjectures
