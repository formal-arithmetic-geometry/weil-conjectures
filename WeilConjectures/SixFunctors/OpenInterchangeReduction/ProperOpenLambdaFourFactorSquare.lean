/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity

/-! # Four-factor ordinary proper/open lambda square

This module isolates the component square for the prescribed four-factor
proper/open lambda.  The recursive word comparison is supplied by the caller.
(blueprint: lem-sf-proper-open-lambda-four-factor-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u s
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction

namespace WeilConjectures.OpenInterchangeReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

namespace FourFactorProof
open IntegralSystemRealization CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [local implicit_reducible] TwoSquare
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  integralOperationsCommHasDerivedCategory
  PurCompactSupport.completed coefficientSequenceHasDerived scalarReductionSourceDerived
  integralTowerHasDerivedCategory integralCompletedRingHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleCanonicalTensorComparison ringedPullComp
  ringedRestrictFactor restrictFactor properOpenLambda ringedProperOpenLambda
  ringedOpenComp Compositors.openComp openCongr ringedOpenCongr

private theorem inverse_square {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {K H : C} {M N : D} (r : K ≅ H) (s : M ≅ N)
    (q : R.obj K ⟶ M) (t : R.obj H ⟶ N)
    (h : q ≫ s.hom = R.map r.hom ≫ t) :
    t ≫ s.inv = R.map r.inv ≫ q := by
  apply (cancel_epi (R.map r.hom)).1
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]

attribute [local irreducible] ringedSquare Compositors.square

private theorem paste_five {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A₀ A₁ A₂ A₃ A₄ A₅ : C} {B₀ B₁ B₂ B₃ B₄ B₅ : D}
    (q₀ : R.obj A₀ ⟶ B₀) (q₁ : R.obj A₁ ⟶ B₁)
    (q₂ : R.obj A₂ ⟶ B₂) (q₃ : R.obj A₃ ⟶ B₃)
    (q₄ : R.obj A₄ ⟶ B₄) (q₅ : R.obj A₅ ⟶ B₅)
    (r₀ : A₀ ⟶ A₁) (r₁ : A₁ ⟶ A₂) (r₂ : A₂ ⟶ A₃)
    (r₃ : A₃ ⟶ A₄) (r₄ : A₄ ⟶ A₅)
    (s₀ : B₀ ⟶ B₁) (s₁ : B₁ ⟶ B₂) (s₂ : B₂ ⟶ B₃)
    (s₃ : B₃ ⟶ B₄) (s₄ : B₄ ⟶ B₅)
    (h₀ : q₀ ≫ s₀ = R.map r₀ ≫ q₁) (h₁ : q₁ ≫ s₁ = R.map r₁ ≫ q₂)
    (h₂ : q₂ ≫ s₂ = R.map r₂ ≫ q₃) (h₃ : q₃ ≫ s₃ = R.map r₃ ≫ q₄)
    (h₄ : q₄ ≫ s₄ = R.map r₄ ≫ q₅) :
    q₀ ≫ s₀ ≫ s₁ ≫ s₂ ≫ s₃ ≫ s₄ = R.map (r₀ ≫ r₁ ≫ r₂ ≫ r₃ ≫ r₄) ≫ q₅ := by
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [R.map_comp, Category.assoc]

@[irreducible] private def restrictionIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {J : B ⥤ C} {K : A ⥤ C} (P : C ⥤ B)
    (cr : F ⋙ J ≅ K) (ur : 𝟭 B ≅ J ⋙ P) : K ⋙ P ≅ F :=
  Functor.isoWhiskerRight cr.symm P ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F ur.symm ≪≫ Functor.rightUnitor _

private theorem inverse_unit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasZeroMorphisms D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : Q ⋙ R ⟶ T ⋙ G) (ur : 𝟭 A ≅ P ⋙ Q) (us : 𝟭 C ≅ F ⋙ G)
    (X : A) (δ : T.obj (P.obj X) ⟶ F.obj (R.obj X))
    [IsIso (((mateEquiv a b).symm χ).natTrans.app X)]
    (hur : ur.hom.app X = a.unit.app X)
    (hus : us.hom.app (R.obj X) = b.unit.app (R.obj X))
    (hδ : δ = GeneratorReduction.inverseOrZero
      (((mateEquiv a b).symm χ).natTrans.app X)) :
    χ.app (P.obj X) ≫ G.map δ ≫ us.inv.app (R.obj X) = R.map (ur.inv.app X) := by
  have hu := GeneratorReduction.inverse_mate_unit_square a b χ (𝟙 (R.obj X))
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hu
  have hx := inverse_square R (ur.app X) (us.app (R.obj X)) (𝟙 _)
    (χ.app (P.obj X) ≫ G.map δ) (by
      simp only [Iso.app_hom, Category.id_comp, hur, hus, hδ]
      exact hu)
  simpa only [Iso.app_inv, Category.comp_id, Category.assoc] using hx

@[irreducible] private def openR (o : IntegralSystemRealization.Operations l E)
    (m : RealizationModel l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    ringedOpen l E j ⋙ (calculus l E V).reduction ⟶
      (calculus l E U).reduction ⋙ IntegralSystemRealization.Operations.shriek l E o j :=
  (NatIso.ofComponents (fun L ↦
    @asIso _ _ _ _ ((m.openReduction l E j).app L)
      (GeneratorReduction.fixedOpenReduction_isIso l E o m j L))
    (fun f ↦ (m.openReduction l E j).naturality f)).inv

private structure Models (o : IntegralSystemRealization.Operations l E) where
  compositors : Compositors l E o
  openComparisons : OpenComparisons l E o compositors
  realizationModel : RealizationModel l E o
  ringedModels : RingedModels l E
  ringedOpenComparisons : RingedOpenComparisons l E ringedModels

attribute [local irreducible] RingedOpenComparisons.unit OpenComparisons.unit

attribute [local irreducible] ringedCartesianConjugate ringedPushComp cartesianConjugate
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  Functor.leftAdjoint

attribute [local irreducible] getLimitCone limit.cone getColimitCocone colimit.cocone
  sheafificationAdjunction presheafToSheaf eqToIso eqToHom

set_option linter.defProp false in
end FourFactorProof

end WeilConjectures.OpenInterchangeReduction
