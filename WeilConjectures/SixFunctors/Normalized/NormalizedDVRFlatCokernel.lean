/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRScalarCokernelComparison
import WeilConjectures.SixFunctors.SheafRestrictionTowerData.StrictRestrictionTower

/-! # Scalar cokernels of strict finite flat DVR models

Source: Stacks Tags 06YS, 06YY, 03EK and 05RT; blueprint DVR effectivity,
proof paragraphs 1--3. (blueprint: lem-coef-normalized-dvr-flat-cokernel).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 30000] SheafOfModules.instPreadditive
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace WeilConjectures
section ExactHelpers
universe a b c v w z
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{z} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (H : A ⥤ B) (R : B ⥤ C) (S : A ⥤ C)
  [H.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  (i : H ⋙ R ≅ S)

end ExactHelpers

section CoefficientComposite
universe a₀ b₀ r₀
variable {C : Type a₀} [Category.{b₀} C] {J : GrothendieckTopology C}
  {coefficient : ℕ → Sheaf J RingCat.{r₀}} {completed : Sheaf J RingCat.{r₀}}

variable [hsh : HasSheafify J AddCommGrpCat.{r₀}]
  [hw : J.WEqualsLocallyBijective AddCommGrpCat.{r₀}]
  [hder : ∀ n, HasDerivedCategory (SheafOfModules.{r₀} (coefficient n))]

attribute [local irreducible] coefficientDerivedComp Functor.mapDerivedCategory

end CoefficientComposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local irreducible] normalizedDVRFlatRestrictionComp

variable (P : ∀ j : ℕ, CochainComplex (normalizedDVRModules l E X j) ℤ)
  (g : ∀ j : ℕ, P (j + 1) ⟶
    ((normalizedDVRModuleRes l E X j.le_succ).mapHomologicalComplex (.up ℤ)).obj (P j))

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralCoefficientSheafSystem normalizedDVRQuotient

attribute [local irreducible] Functor.mapDerivedCategory

section TowerCoherence

end TowerCoherence

attribute [local irreducible] finiteChainComp

end WeilConjectures
