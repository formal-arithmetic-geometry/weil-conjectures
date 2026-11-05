/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.ConstantToContinuousScalarFlat
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModelResolution

/-!
# Two-term resolutions of finite constant scalar models

Source: Bhatt--Scholze, Proposition 6.8.11(3), Lemma 6.8.2(1); Stacks Tags 093J,
093M (blueprint: lem-sfb-finite-constant-model-two-term-free-resolution).

The model functor first forms discrete constant modules, extends scalars by the map
sending a scalar to the constant continuous function, and applies the monoidal inverse
image from the point. Thus it is precisely B_T tensor over the discrete constant A,
not a tensor over the continuous coefficient ring on the point.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteConstantModel

variable (A : Type u) [CommRing A]

variable [TopologicalSpace A] [IsTopologicalRing A]

attribute [instance] scalarToContinuous_isMonHom

set_option linter.unusedSectionVars false in
attribute [instance] constantScalars_commutative

end AlgebraicGeometry.ProEtale.FiniteConstantModel

namespace AlgebraicGeometry.ProEtale.FiniteConstantModel

universe uC vC

section FreeModels

variable (A : Type u) [CommRing A]

variable [TopologicalSpace A] [IsTopologicalRing A]

end FreeModels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry.ProEtale.FiniteConstantModel
