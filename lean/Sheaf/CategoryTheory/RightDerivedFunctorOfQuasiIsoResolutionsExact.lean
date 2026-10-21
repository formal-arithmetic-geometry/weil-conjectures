/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-!
# Right derived functors of exact functors

Source: blueprint order 1610, `def-sfb-right-derived-exact`; Stacks Project,
Derived Categories, lemma-right-derived-exact-functor
(blueprint: def-sfb-right-derived-exact).
-/

@[expose] public section

set_option autoImplicit false

universe wC wD vC vD uC uD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive]
  (h : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The canonical comparison of the recorded right derived functor with termwise F.
Source: blueprint order 1610; Stacks Project, Derived Categories,
lemma-right-derived-exact-functor (blueprint: def-sfb-right-derived-exact).

Construction: exactness preserves cohomology and quasi-isomorphisms, so Mathlib's
mapDerivedCategory descends termwise F and mapDerivedCategoryFactorsh identifies its
composite with Qh. Its inverse is a right-derived unit by
isRightDerivedFunctor_of_inverts. The universal pair of def-sfb-right-derived-functor
therefore supplies a unique isomorphism compatible with these units. The choice below
is from that unique characterization, not from an unconstrained existence claim. -/
noncomputable def rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory :
    F.rightDerivedFunctorOfQuasiIsoResolutions h ≅ F.mapDerivedCategory :=
  letI := isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  letI := IsRightDerivedFunctor.isLeftKanExtension F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh.inv (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  Classical.choose (ExistsUnique.exists
    (F.rightDerivedFunctorOfQuasiIsoResolutions_unique h F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh.inv (fun G ↦
        (F.mapDerivedCategory.homEquivOfIsLeftKanExtension
          F.mapDerivedCategoryFactorsh.inv G).bijective)))

/-- The comparison preserves the specified right-derived units.
Source: blueprint order 1610; Stacks Project, Derived Categories,
lemma-right-derived-exact-functor (blueprint: def-sfb-right-derived-exact).

Proof plan:
1. Exactness makes termwise F preserve quasi-isomorphisms, giving mapDerivedCategory
   and the factorization isomorphism mapDerivedCategoryFactorsh.
2. Its inverse is a universal right-derived unit by isRightDerivedFunctor_of_inverts.
3. Apply the unique comparison of def-sfb-right-derived-functor to that pair. The
   definition chooses this unique comparison, whose defining property is this equation. -/
theorem rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory_hom_fac :
    F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (F.rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory h).hom =
      F.mapDerivedCategoryFactorsh.inv := by
  let := isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  let := IsRightDerivedFunctor.isLeftKanExtension F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh.inv (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  exact Classical.choose_spec (ExistsUnique.exists
    (F.rightDerivedFunctorOfQuasiIsoResolutions_unique h F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh.inv (fun G ↦
        (F.mapDerivedCategory.homEquivOfIsLeftKanExtension
          F.mapDerivedCategoryFactorsh.inv G).bijective)))

end CategoryTheory.Functor
