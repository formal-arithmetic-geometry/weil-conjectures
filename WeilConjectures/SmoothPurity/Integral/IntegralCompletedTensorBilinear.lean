/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear

import all WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.SmoothPurity.Integral.IntegralDerivedPullbackLinear
import WeilConjectures.Algebra.Homology.BifunctorLinear
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Constant-scalar bilinearity of the normalized integral completed tensor

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4); Stacks Project,
Tags 06YS and 099N; the assigned integral-to-rational tensor construction.
(blueprint: lem-sf-integral-completed-tensor-bilinear).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

open CategoryTheory.Limits Opposite TensorProduct
open scoped ChangeOfRings

section TensorRepresentatives

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

attribute [local instance] coefficientModuleLinear
attribute [local instance 3000] integralCoefficientLinear
attribute [local irreducible] unrestrictedIntegralReductionExistence HasDerivedCategory.standard

attribute [local instance] finiteSheafLinear

attribute [local instance] finiteLinear

attribute [local irreducible] integralOperationsTensorComplexFunctor

end TensorRepresentatives

section TensorDescent

attribute [local instance] coefficientModuleLinear
attribute [local instance 3000] integralCoefficientLinear

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

end TensorDescent

end WeilConjectures
