/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import Submission.WeilConjectures.ConstructibleSheaf.Pullback
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Condensed.TopComparison
public import Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Submission.WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import Submission.WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Submission.WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Submission.WeilConjectures.TateTwist.ProEtale
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Submission.WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Free integral modules on finite constant coefficients

Source: the coefficient quotient comparison in the blueprint Tate-twist construction.
(blueprint: lem-poincare-integral-residue-free-comparison)
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory Opposite Preadditive MonObj
open scoped Topology CategoryTheory.Obj
open Filter
namespace PadicInt
variable {p : ℕ} [Fact p.Prime]
end PadicInt
namespace AlgebraicGeometry.ProEtale
open CondensedRing
end AlgebraicGeometry.ProEtale

namespace AddCommGrpCat
end AddCommGrpCat

namespace AlgebraicGeometry.ProEtale
universe v w
end AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale
open CondensedRing
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
private instance freeFunctorAdditive (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.freeFunctor R).Additive :=
  { map_add := by
      intro A B f g
      apply Mod.hom_ext
      exact MonoidalPreadditive.whiskerLeft_add f g }

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
/-- Reduction between the finite constant abelian coefficient groups. -/
noncomputable def integralResidueAbTransition (ℓ n : ℕ) :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))) ⟶
      AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))) :=
  AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n))).toAddMonoidHom.comp
      AddEquiv.ulift.toAddMonoidHom))
/-- The constant finite coefficient tower, including its zero level. -/
noncomputable def constantTateResidueSystem (X : Scheme.{u}) (ℓ : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))
    (integralResidueAbTransition.{u} ℓ) ⋙
    constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
end AlgebraicGeometry.ProEtale
