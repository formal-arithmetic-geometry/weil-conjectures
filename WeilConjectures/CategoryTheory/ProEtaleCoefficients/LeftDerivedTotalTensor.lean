/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Left derived functors computed on K-flat complexes

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-def-sfb-derived-categories`, `def-sfb-left-derived-functor`
(blueprint: def-sfb-left-derived-functor).

The functor and its counit are Mathlib's canonical total left derived functor and
counit. This interface uses the binary total-tensor K-flatness recorded by the
statement dependency, without requiring a chosen monoidal structure on complexes.

## Main definitions

* `CategoryTheory.Functor.leftDerivedFunctorFromTotalTensor`: the total left derived functor.
* `CategoryTheory.Functor.leftDerivedFunctorFromTotalTensorCounit`: its canonical counit.
-/

@[expose] public section

universe uC vC uD vD wC wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalPreadditive C]
  [hCountable : HasCountableCoproducts C] [hIntColimits : HasColimitsOfShape ℤ C]
  [hExactIntColimits : HasExactColimitsOfShape ℤ C]
  [hTensorLeft : ∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [hTensorRight : ∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [hFlatResolution : Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [hF : F.PreservesTotalTensorKFlatQuasiIso]

omit hExactIntColimits hTensorLeft hFlatResolution [HasDerivedCategory C] in
attribute [local instance] preservesCountableTensorLeft preservesCountableTensorRight

omit hExactIntColimits hTensorRight hFlatResolution [HasDerivedCategory C] in
attribute [local instance] hasTensorFour hasGoodTensorLeft hasGoodTensorRight

omit hExactIntColimits hFlatResolution [HasDerivedCategory C] [HasDerivedCategory D] in
attribute [local instance] preservesKFlatQuasiIso

end CategoryTheory.Functor
