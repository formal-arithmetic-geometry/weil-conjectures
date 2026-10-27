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

local instance : (localizedSystemExtension.{c, v, r} R V).Additive :=
  localizedSystemExtensionAdditive.{c, v, r} R V
local instance : PreservesFiniteLimits (localizedSystemExtension.{c, v, r} R V) :=
  localizedSystemExtensionLimits.{c, v, r} R V
local instance : PreservesFiniteColimits (localizedSystemExtension.{c, v, r} R V) :=
  localizedSystemExtensionColimits.{c, v, r} R V

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
  normalized :
    letI := base.scalar.additive
    letI := slice.scalar.additive
    letI := localizedSystemExtensionAdditive.{c, v, r} R V
    letI := localizedSystemExtensionLimits.{c, v, r} R V
    letI := localizedSystemExtensionColimits.{c, v, r} R V
    letI := localizedSystemExtensionAdditive.{c, v, r} (S.obj n).right V
    letI := localizedSystemExtensionLimits.{c, v, r} (S.obj n).right V
    letI := localizedSystemExtensionColimits.{c, v, r} (S.obj n).right V
    NormalizedExactDescent
      (A := Modules.{max c v, v, r} (R.over V)) (B := Modules.{c, v, r} R)
      (C := Modules.{max c v, v, r}
        ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)).right)
      (D := Modules.{c, v, r} (S.obj n).right)
      (localizedSystemExtension.{c, v, r} R V)
      (localizedSystemExtension.{c, v, r} (S.obj n).right V)
      base.scalar.E slice.scalar.E base.scalar.T slice.scalar.T
      base.scalar.ε slice.scalar.ε (Resolving.{max c v, v, r} (R.over V)) ordinary derived
  /-- The evaluated rho is scalar restriction of the linear derived comparison. -/
  evaluated :
    letI := localizedSystemExtensionAdditive.{c, v, r} R V
    letI := localizedSystemExtensionLimits.{c, v, r} R V
    letI := localizedSystemExtensionColimits.{c, v, r} R V
    letI := localizedSystemExtensionAdditive.{c, v, r} (S.obj n).right V
    letI := localizedSystemExtensionLimits.{c, v, r} (S.obj n).right V
    letI := localizedSystemExtensionColimits.{c, v, r} (S.obj n).right V
    DerivedEvaluationSquare
      (A := Modules.{max c v, v, r} (R.over V)) (B := Modules.{c, v, r} R)
      (C := ℕᵒᵖ ⥤ Modules.{max c v, v, r} (R.over V))
      (D := ℕᵒᵖ ⥤ Modules.{c, v, r} R)
      (E := Modules.{max c v, v, r}
        ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)).right)
      (F := Modules.{c, v, r} (S.obj n).right)
      (localizedSystemExtension.{c, v, r} R V) (towerExtension.{c, v, r} R V)
      (evaluation.{c, v, r} R n) (evaluation.{max c v, v, r} (R.over V) n)
      (localizedSystemExtension.{c, v, r} (S.obj n).right V)
      (scalars.{c, v, r} R (S.obj n))
      (scalars.{max c v, v, r} (R.over V)
        ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)))
      (m.F.obj S) (mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V))
      base.scalar.T slice.scalar.T
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) restriction
      ρ base.derived slice.derived derived

end SheafOfModules.LocalizedStrictTensor
