/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Submission.WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Submission.WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import Submission.WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

import Submission.WeilConjectures.Algebra.Homology.RoosCoordinatesQuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import Submission.WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
public import Submission.WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Derived completion for pulled-back continuous integral coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-def-pe-derived-completion/_section.md` (blueprint: sk-def-pe-derived-completion).

The coefficient objects are the continuous condensed rings of DerivedNakayama,
pulled back by the published strong monoidal inverse image from the point.
Positive level n is indexed by n-1. Completion uses the explicit augmented Roos
complex on a K-flat representative, with zero homotopy in its second coordinate.
Normalization uses extension of scalars over the successive finite coefficient rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] ringMonoidalObject ringCommutative finiteRingMonoidalObject
  finiteRingCommutative modulesMonoidal modulesSymmetric modulesClosed modulesMonoidalPreadditive
  finiteModulesDerived modulesDerived modulesProducts complexProducts
  modulesNatProducts complexNatProducts complexNatLimit

private theorem quotientUnit_step (n : ℕ) :
    quotientUnit l E (n + 1) ≫ quotientStep l E n = quotientUnit l E n := by
  apply Mod.hom_ext
  rfl

private theorem finiteUnit_step (X : Scheme.{u}) (n : ℕ) :
    finiteUnit l E X (n + 1) ≫
      (DerivedNakayama.pullback l E X).map (quotientStep l E n) = finiteUnit l E X n := by
  dsimp only [finiteUnit]
  rw [Category.assoc, ← Functor.map_comp, quotientUnit_step]

private theorem levelUnit_step (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ)
    (n : ℕ) : levelUnit l E X P (n + 1) ≫ levelStep l E X P n = levelUnit l E X P n := by
  apply HomologicalComplex.hom_ext
  intro i
  change ((ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X (n + 1)) ≫
    P.X i ◁ (DerivedNakayama.pullback l E X).map (quotientStep l E n) =
    (ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X n
  rw [Category.assoc, ← whiskerLeft_comp, finiteUnit_step]

end AlgebraicGeometry.ProEtale.AdicCompletion

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts
  AdicCompletion.modulesNatProducts AdicCompletion.complexNatProducts
  AdicCompletion.complexNatLimit

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint
attribute [local instance] ringMonoidalObject ringCommutative finiteRingMonoidalObject
  finiteRingCommutative modulesMonoidal modulesSymmetric modulesClosed
  modulesMonoidalPreadditive finiteModulesDerived modulesDerived modulesProducts complexProducts
  modulesNatProducts complexNatProducts complexNatLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

end AlgebraicGeometry.ProEtale.AdicCompletion

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint
attribute [local instance] ringMonoidalObject ringCommutative finiteRingMonoidalObject
  finiteRingCommutative modulesMonoidal modulesSymmetric modulesClosed
  modulesMonoidalPreadditive finiteModulesDerived modulesDerived modulesProducts complexProducts
  modulesNatProducts complexNatProducts complexNatLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})



end AlgebraicGeometry.ProEtale.AdicCompletion
