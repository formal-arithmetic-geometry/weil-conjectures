/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Algebra.Homology.LocalizedStrictTensorData

/-! # Normalized localized extension on derived strict coefficient towers

Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor;
Cohomology on Sites, Tags 06YS and 06YU; Categories, Tags 04VG and 04VK.
(blueprint: def-sf-localized-strict-tensor-linear-evaluation-data).

Strict towers are localized after taking complexes. The reduction functor is the
universal left derived functor of the actual ordinary tensor tower, equivalently
the diagram-site tensor of the constant diagram with the coefficient tower.
The counit fixes all representative comparisons; no functorial resolution is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace SheafOfModules.LocalizedStrictTensor
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- Full coefficient-linear evaluation data, fixed at the ordinary and derived levels.
The final equation says literally that evaluation of rho is scalar restriction of kappa.
Source: Stacks 0E8I and 06YU
(blueprint: def-sf-localized-strict-tensor-linear-evaluation-data). -/
structure LinearEvaluation
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V)
    (ρ : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ m.F.obj S ≅
      mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        (towerExtension.{c, v, r} R V).mapDerivedCategory) where
  /-- Canonically normalized evaluation on the base site. -/
  base : EvaluationModel.{c, v, r} R m S n
  /-- Canonically normalized evaluation on the slice site. -/
  slice : EvaluationModel.{max c v, v, r} (R.over V) mV
    (S ⋙ sliceAlgebras.{c, v, r} R V) n
  /-- Underlying extension is extension after scalar restriction. -/
  restriction :
    scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} (S.obj n).right V ⋙
        scalars.{c, v, r} R (S.obj n)
  /-- The comparison preserves extension generators. -/
  restriction_normalized : ScalarExtensionNormalized.{c, v, r} R V (S.obj n) restriction
  /-- The genuinely S_n-linear ordinary projection comparison. -/
  ordinary : localizedSystemExtension.{c, v, r} R V ⋙ base.scalar.E ≅
    slice.scalar.E ⋙ localizedSystemExtension.{c, v, r} (S.obj n).right V
  /-- After restricting coefficients it is exactly the specified tower component. -/
  ordinary_square : ∀ M : Modules.{max c v, v, r} (R.over V),
    (η.hom.app M).app n ≫
      (localizedSystemExtension.{c, v, r} R V).map (slice.ordinary.hom.app M) ≫
      restriction.hom.app (slice.scalar.E.obj M) =
    base.ordinary.hom.app ((localizedSystemExtension.{c, v, r} R V).obj M) ≫
      (scalars.{c, v, r} R (S.obj n)).map (ordinary.hom.app M)
  /-- The coefficient-linear derived projection comparison. -/
  derived : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ base.scalar.T ≅
    slice.scalar.T ⋙
      (localizedSystemExtension.{c, v, r} (S.obj n).right V).mapDerivedCategory
  /-- Its component on every resolving representative is the localized linear chain map. -/
  normalized : ∀ (P : CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ),
    Resolving.{max c v, v, r} (R.over V) P →
    base.scalar.T.map
      ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategoryFactors.hom.app P) ≫
    base.scalar.ε.app
      (((localizedSystemExtension.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map ((scalarComparisonOnComplexes.{c, v, r} R V (S.obj n)
      base.scalar slice.scalar ordinary).hom.app P) =
    derived.hom.app (DerivedCategory.Q.obj P) ≫
    (localizedSystemExtension.{c, v, r} (S.obj n).right V).mapDerivedCategory.map
      (slice.scalar.ε.app P) ≫
    (localizedSystemExtension.{c, v, r} (S.obj n).right V).mapDerivedCategoryFactors.hom.app
      ((slice.scalar.E.mapHomologicalComplex (.up ℤ)).obj P)
  /-- The evaluated rho is scalar restriction of the linear derived comparison. -/
  evaluated : ∀ K : D.{max c v, v, r} (R.over V),
    (evaluation.{c, v, r} R n).mapDerivedCategory.map (ρ.hom.app K) ≫
      (evaluationExtensionDerived.{c, v, r} R V n).hom.app
        ((mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V)).obj K) ≫
      (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory.map
        (slice.derived.hom.app K) ≫
      (scalarExtensionDerived.{c, v, r} R V (S.obj n) restriction).hom.app
        (slice.scalar.T.obj K) =
    base.derived.hom.app ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategory.obj K) ≫
      (scalars.{c, v, r} R (S.obj n)).mapDerivedCategory.map (derived.hom.app K)

end SheafOfModules.LocalizedStrictTensor
