/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceConstruction
public import WeilConjectures.SixFunctors.AdicQbarRealization.ScalarSourceCalculus.AdicReindexSourceCalculus

/-! # Component assembly of the source scalar square

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-source-assembly)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] HasDerivedCategory.standard
  derivedPull LocallyFiniteAdicRealization.sections
  LocallyFiniteAdicRealization.CoefficientPresentation.integralMap
  podCompletedDerivedInverseImage integralDerivedPullback
  commonStageDerivedPullback rationalDerivedPullback

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem integralTransition)

open ScalarSourceCalculus

attribute [local implicit_reducible] StageSystem.ι
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  integralScalarExtensionOfUniverses

-- Keep the selected comparison maps abstract while checking the final square.
attribute [local irreducible] completedScalarReindex completedReindexModel scalarExactModel
  integralPullbackScalarComparison podCompletedToTowerIso pbcReductionNormalization
  pbcReductionNormalizationHom pbcReductionTransition
  podCompletedToTower pbcDerivedScalarAdjunction
attribute [local implicit_reducible] ordinary coefficientMap
  LocallyFiniteAdicRealization.ringSheaf AlgebraicGeometry.Scheme.residueField

/-- Store the actual source-scalar diagram as concrete data.
Source: BS Remark 6.8.15 and Proposition 6.8.14.
(blueprint: lem-sf-adic-reindex-source-assembly).
Every field is the specified map; no choice or existence theorem enters this packaging. -/
def sourceScalarMaps (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    ScalarSourceMaps
      (DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) X))
      (DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) L) X))
      (DerivedCategory (modules l X R)) := by
  let C := Coefficient.{u} l (PadicAlgCl l)
  let i := coefficientInclusion l (PadicAlgCl l) E L h
  let P (F : Index l (PadicAlgCl l)) := constructibleIntegralPullback l (C F) g
  let Q (W : Scheme.{u}) (F : Index l (PadicAlgCl l)) :=
    sfRationalConstructibleLocalization l (C F) W
  let I (W : Scheme.{u}) (F : Index l (PadicAlgCl l)) :=
    inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) F
  let F := commonStageDerivedPullback l (PadicAlgCl l) g
  let O := ordinary l X R
  let NE := pbcDerivedExtend (coefficientMap l X R E)
  let NL := pbcDerivedExtend (coefficientMap l X R L)
  let T := pbcDerivedExtend (completedCoefficientMap l (C E) (C L) i X)
  let KL := (integralTransition l (PadicAlgCl l) Y E L h).obj K
  let KE := (P E).obj K
  let δ := (integralPullbackScalarComparison l (C E) (C L) i g K).hom
  let e (J : Index l (PadicAlgCl l)) :=
    (congrArg (fun Z ↦ Q Y J ⋙ Z) (realizationPullback_inclusion_eq l g J)).trans
      (congrArg (fun Z ↦ Z ⋙ I X J) (realizationPullback_localization_eq l g J))
  let aY := realizationScalarArrow l Y E L h K
  let φ := completedCoefficientMap l (C E) (C L) i X
  let ψ := coefficientMap l X R L
  let χ := coefficientMap l X R E
  let hh := R.coefficient_scalar E L h
  refine {
    NE := NE, NL := NL, T := T
    E := _, P := _, F := _, Q := _, M := _, Z := _, A := _, B := _, U := _, V := _
    p := podCompletedToTowerIso l (C E) g K
    q := podCompletedToTowerIso l (C L) g KL
    r₀ := O.map (eqToHom (Functor.congr_obj (e E) K))
    r₁ := (R.integral E).hom.app KE
    s₀ := O.map (eqToHom (Functor.congr_obj (e L) KL))
    s₁ := (R.integral L).hom.app ((P L).obj KL)
    f := (F ⋙ O).map aY
    χ := (completedScalarComparison l (C E) (C L) i X).app KE.obj
    δ := δ.hom
    b := (completedScalarReindex l (C E) (C L) i g).hom.app K.obj
    c := (podCompletedDerivedInverseImage l (C L) g).map
      ((completedScalarComparison l (C E) (C L) i Y).app K.obj)
    srcE := (realizationReindexSource l g R E).hom.app K
    srcL := (realizationReindexSource l g R L).hom.app KL
    n := fun M ↦ (pbcReductionNormalization φ ψ χ hh M).inv
    naturality := normalization_inv_naturality φ ψ χ hh _ }

end WeilConjectures.AdicQbarRealization
