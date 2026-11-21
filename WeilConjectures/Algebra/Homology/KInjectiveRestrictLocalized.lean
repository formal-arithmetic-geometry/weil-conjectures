/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Restriction to a localized ringed site preserves K-injectivity

## References

* Stacks Project, Tag 08FI (Lemma 21.20.1), also used in Tag 0A94
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction of a K-injective module complex to C/U is K-injective, for any
Grothendieck topology on C. -/
theorem isKInjective_restrict_localized
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms)
    (I : CochainComplex (SheafOfModules.{max u v} R) ℤ) [I.IsKInjective] :
    letI := hzero
    CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{max u v} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let := hzero
  obtain ⟨G, hlimits, hcolimits, hadd, ⟨adj⟩⟩ := localized_restriction_adjunction R U hzero
  let : PreservesFiniteLimits G := hlimits
  let : PreservesFiniteColimits G := hcolimits
  let : G.IsLeftAdjoint := adj.isLeftAdjoint
  let : G.Additive := G.additive_of_preserves_binary_products
  let : (SheafOfModules.overFunctor.{max u v} R U).Additive := hadd
  let : (SheafOfModules.overFunctor.{max u v} R U).PreservesKInjectiveComplexes :=
    adj.preservesKInjectiveComplexes
  exact Functor.PreservesKInjectiveComplexes.isKInjective_map I


end CategoryTheory
