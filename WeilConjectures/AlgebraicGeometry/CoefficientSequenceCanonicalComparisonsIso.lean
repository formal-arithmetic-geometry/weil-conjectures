/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCanonicalComparisons
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceExactProducts
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.Products

/-! # Invertibility of the canonical coinduced product comparisons

Source: Stacks 079P and 0941.
(blueprint: lem-coef-sequence-canonical-comparisons-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.CoefficientCoinduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

set_option maxHeartbeats 2000000 in
-- The product fans contain several exact-functor comparisons over the sequence site.
/-- Localization preserves these products because products of pro-etale module sheaves
are exact; the existing coefficient-sequence exact-products theorem supplies exactness.
The localized projection fans are limits. Their componentwise exact-functor isomorphisms
identify their points with the specified derived products, hence the canonical lifts are
invertible. Source: Stacks 079P and 0941.
(blueprint: lem-coef-sequence-canonical-comparisons-iso). -/
theorem canonicalComparisons_isIso
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    IsIso (canonicalProductComparison l E W K) ∧
      IsIso (canonicalRelationsComparison l E W K) := by
  have := sequence_exact_products l E W
  have : IsGrothendieckAbelian.{u + 1} (coefficientSequenceModules l E W) :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
  have : Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E W) := by
    infer_instance
  constructor
  · exact Fan.IsLimit.isIso_of_isos
      (DerivedCategory.isLimitFanMkQObj (productIsProduct _))
      (productIsProduct _) (canonicalProductFactorComparison l E W K)
      (canonicalProductComparison l E W K) (fun n ↦ Pi.lift_π _ n)
  · exact Fan.IsLimit.isIso_of_isos
      (DerivedCategory.isLimitFanMkQObj (productIsProduct _))
      (productIsProduct _) (canonicalRelationsFactorComparison l E W K)
      (canonicalRelationsComparison l E W K) (fun n ↦ Pi.lift_π _ n)

end WeilConjectures.CoefficientCoinduction
