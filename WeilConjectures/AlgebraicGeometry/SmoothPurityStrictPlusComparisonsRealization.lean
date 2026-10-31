/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictCompactificationComparisonData

/-! # Bounded-below adjunction comparison for strict compactification data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
section Restriction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives D] [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]

private theorem comparison_restrict_derived_adjunction (adj : f ⊣ g) :
    Adjunction.restrictFullyFaithful adj.mapDerivedCategoryRightDerivedAdjunction
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      f.mapDerivedCategoryPlusCompatibility.symm
      g.rightDerivedFunctorPlusCompatibility.symm = adj.derivedPlus := by
  apply Adjunction.ext
  apply adj.derivedPlus_unit_eq
  intro K
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, Adjunction.map_restrictFullyFaithful_unit_app]
  have h₁ := adj.mapHomotopyCategory (ComplexShape.up ℤ) |>.derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.mapDerivedCategoryFactorsh.hom
    g.rightDerivedFunctorUnit K.obj
  have h₃ : g.rightDerivedFunctorPlusιUnit.app (f.mapHomotopyCategoryPlus.obj K) ≫
      g.rightDerivedFunctorPlusCompatibility.hom.app
        (DerivedCategory.Plus.Qh.obj (f.mapHomotopyCategoryPlus.obj K)) =
      g.ιRightDerivedFunctorUnit.app (f.mapHomotopyCategoryPlus.obj K) := by
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  have h₄ : DerivedCategory.Plus.ι.map
      (g.rightDerivedFunctorPlusUnit.app (f.mapHomotopyCategoryPlus.obj K)) =
      g.ιRightDerivedFunctorUnit.app (f.mapHomotopyCategoryPlus.obj K) ≫
        g.rightDerivedFunctorPlusCompatibility.inv.app
          (DerivedCategory.Plus.Qh.obj (f.mapHomotopyCategoryPlus.obj K)) := by
    rw [← h₃, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h₅ := g.rightDerivedFunctorPlusCompatibility.inv.naturality
    (f.mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.comp_map, Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app] at h₅
  have h₇ : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K.obj) := by
    exact congrArg DerivedCategory.Qh.map
      (Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app adj K)
  rw [h₄, h₇]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app, Iso.symm_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.assoc, ← h₅, ← Category.assoc, h₁, Category.assoc]
  rfl

end Restriction

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The unbounded adjunction comparisons restrict to the bounded-below
comparisons for every strict geometric operation.
Source: blueprint operations proof (2); Stacks 05TI, 070J.
(blueprint: lem-sp-strict-plus-comparisons-realization).

Proof: restrict the canonical right-derived adjunction along the fully faithful
inclusion of bounded-below derived categories. The unit and counit are the
images of the ordinary derived unit and counit by the canonical comparison
isomorphisms. Uniqueness of the right derived adjunction identifies this
restricted adjunction with `ordinaryAdjunction.derivedPlus`; the displayed
left and right comparison maps are therefore exactly the canonical ones.
The restriction identity is checked after the fully faithful inclusion using
unit uniqueness and the derived-unit factorization. -/
theorem strictPlusComparisonsRealization (b : Base l E) (o : Operations l E b)
    [∀ T : Scheme.{u}, EnoughInjectives (S l E T)] :
    StrictPlusComparisons l E b o := by
  intro X Y f
  let g := o.geometry f
  let a := g.ordinaryAdjunction
  have ha := comparison_restrict_derived_adjunction a
  refine ⟨{ left := g.pull.mapDerivedCategoryPlusCompatibility
            right := g.push.rightDerivedFunctorPlusCompatibility
            unit := ?_
            counit := ?_ }, rfl, rfl⟩
  · intro K
    rw [← ha, Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, push, adjunction, a, g,
      Functor.id_obj, ObjectProperty.ι_obj, Functor.comp_obj, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_app_assoc, cancelIso, Category.comp_id]
  · intro K
    rw [← ha, Adjunction.map_restrictFullyFaithful_counit_app]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, pull, adjunction, a, g,
      Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj, Iso.symm_inv,
      Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.ProEtale.SpTowerShriek
