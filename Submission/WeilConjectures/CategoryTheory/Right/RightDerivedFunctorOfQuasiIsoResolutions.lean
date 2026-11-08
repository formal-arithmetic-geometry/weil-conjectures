/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Right derived functors using arbitrary K-injective resolutions

Source: blueprint `def-sfb-right-derived-functor`, order 1609; Stacks Project,
Derived Categories, Tags 070K and 070Y (blueprint: def-sfb-right-derived-functor).

The upstream `Functor.rightDerivedFunctor` requires monomorphic resolutions. Here the
hypothesis is precisely that of Tag 070K. We choose a universal pair supplied by
`exists_rightDerived_of_enough_isKInjective`; its universal property determines it up to
unique isomorphism compatible with its unit.
-/

@[expose] public section

set_option autoImplicit false

universe wC wD vC vD uC uD

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive]
  (h : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

/-- The functor of the universal right-derived pair. Source: blueprint order 1609,
Stacks Tags 070K and 070Y (blueprint: def-sfb-right-derived-functor).
The pair is determined up to unique isomorphism by its universal property. -/
noncomputable def rightDerivedFunctorOfQuasiIsoResolutions :
    DerivedCategory C ⥤ DerivedCategory D :=
  Classical.choose (exists_rightDerived_of_enough_isKInjective h
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))

end CategoryTheory.Functor
