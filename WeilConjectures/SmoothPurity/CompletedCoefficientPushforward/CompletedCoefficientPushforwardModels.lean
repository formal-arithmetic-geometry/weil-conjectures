/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

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
/-!
# Models for completed-coefficient direct image and its strict quotient tower

(blueprint: def-pur-completed-pushforward-models).

Source: Stacks Tags 0D6E, 0A07 and 099N (1),(4); blueprint fix-prop-adjunctions, Step 1
(blueprint: lem-pur-completed-coefficient-pushforward-comparison).

All sites retain their object and morphism universes. The auxiliary records retain
universal derived units and representative normalizations; their existence is a conclusion.
The constructions and signatures are the existing completed-coefficient comparison interface.
They are re-exported by CompletedCoefficientPushforwardComparison; the extraction permits
its independent proof lemmas to use the interface without an import cycle.

## Main definitions and statement

- `RightImage`, `ExactImage`, and `Square`: derived models and their normalized comparisons.
- `SiteData`: exact scalar restrictions, strict coefficient systems, and derived tower limits.
- `ComparisonData`: coefficient coherence, strict diagrams, and complete reconstruction.
- `ComparisonData.completeComparison`: the comparison restricted to complete source objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b av bv c cv z zv d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward

section DerivedModels
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) [F.PreservesZeroMorphisms]

end DerivedModels

section Squares
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type z} [Category.{zv} D] [Abelian D] [HasDerivedCategory.{d} D]
  (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [V.PreservesZeroMorphisms]
  (RF : RightImage F) (RG : RightImage G) (DU : ExactImage U) (DV : ExactImage V)

end Squares

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [instance] SystemRestrictionData.systemRestrictionAdditive

variable {X Y : Scheme.{t}} (f : X ⟶ Y)

attribute [instance] CoefficientImageData.completedAdditive

end WeilConjectures.CompletedCoefficientPushforward
