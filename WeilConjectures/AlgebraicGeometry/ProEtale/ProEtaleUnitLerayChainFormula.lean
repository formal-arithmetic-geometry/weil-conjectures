/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# The ordinary pro-etale unit--Leray chain formula

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08J6 and 0D6E;
derived.tex, Tags 070I, 08BJ and 0FND
(blueprint: lem-trf-proetale-unit-leray-chain-formula).

The module and derived units are those of the recorded constant-ring adjunction.
The terminal comparison uses its sectionwise direct image, identified with the canonical
fixed-scalar realization by the published section-normalized comparison. Thus its final
map is evaluation at the actual terminal base change, X times_Y Y = X.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

section UnitLerayCalculation

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  {L : D ⥤ C} {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [L.Additive] [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [F.PreservesKInjectiveComplexes] (a : L ⊣ F) (e : F ⋙ G ≅ H)

-- The composition comparison carries the composite derived unit to the derived unit.

-- Compute before inverting units; no K-injectivity is required at this stage.

-- Naturality in j and inversion of the units at I and J give the chain representative.

end UnitLerayCalculation

end AlgebraicGeometry.Scheme
