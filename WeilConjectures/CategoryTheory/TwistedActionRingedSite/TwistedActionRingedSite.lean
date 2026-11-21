/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionSiteRestriction
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionClosedComparisons
import WeilConjectures.CategoryTheory.Endofunctor.FixedPairCreatedLimits
import WeilConjectures.CategoryTheory.Endofunctor.EquivalenceOrbitInduction
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-! # The ringed site of a site automorphism

The site restriction and closed comparisons are combined with created fixed-pair limits
and exact integer-orbit induction. All data are re-exported from the data module.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

omit [s.functor.IsContinuous J J] in
/-- Canonical small-limit lifting for the module translation forgetful functor.

For each diagram, compose the generic full-subcategory and endofunctor-algebra lifts.
The module-sheaf limit exists, and translation preserves it because it is an equivalence.
-/
noncomputable instance translationForgetCreatesLimits [(sigma J s R a).IsEquivalence] :
    CreatesLimitsOfSize.{u, u} (Endofunctor.IsoAlgebra.forget (sigma J s R a)) := by
  change CreatesLimitsOfSize.{u, u}
    ((Endofunctor.Algebra.IsIsoStr (sigma J s R a)).ι ⋙
      Endofunctor.Algebra.forget (sigma J s R a))
  exact ⟨fun {_} _ ↦ inferInstance⟩

/-- Canonical small-colimit lifting for the module translation forgetful functor.

For each diagram, compose the generic full-subcategory and endofunctor-algebra lifts.
The module-sheaf colimit exists, and translation preserves it because it is an equivalence.
-/
noncomputable instance translationForgetCreatesColimits [(sigma J s R a).IsEquivalence] :
    CreatesColimitsOfSize.{u, u} (Endofunctor.IsoAlgebra.forget (sigma J s R a)) := by
  change CreatesColimitsOfSize.{u, u}
    ((Endofunctor.Algebra.IsIsoStr (sigma J s R a)).ι ⋙
      Endofunctor.Algebra.forget (sigma J s R a))
  exact ⟨fun {_} _ ↦ inferInstance⟩

omit [s.functor.IsContinuous J J] in
private theorem addLimits (P : RestrictionPresentation J s R a) :
    Nonempty (ModulePresentation J s R a) := by
  have : (sigma J s R a).IsEquivalence := by
    rw [← P.translation_eq]
    infer_instance
  have : (sigma J s R a).Additive := by
    constructor
    intro M N f g
    ext X x
    rfl
  exact ⟨{
    toRestrictionPresentation := P
    conservative := inferInstanceAs
      (Endofunctor.IsoAlgebra.forget (sigma J s R a)).ReflectsIsomorphisms
    createsLimits := inferInstanceAs
      (CreatesLimitsOfSize.{u, u} (Endofunctor.IsoAlgebra.forget (sigma J s R a)))
    createsColimits := inferInstanceAs
      (CreatesColimitsOfSize.{u, u} (Endofunctor.IsoAlgebra.forget (sigma J s R a)))
    exact_limits := inferInstanceAs
      (PreservesFiniteLimits (Endofunctor.IsoAlgebra.forget (sigma J s R a)))
    exact_colimits := inferInstanceAs
      (PreservesFiniteColimits (Endofunctor.IsoAlgebra.forget (sigma J s R a))) }⟩

omit [s.functor.IsContinuous J J] in
private theorem addOrbit (P : ModulePresentation J s R a) :
    Nonempty (OrbitPresentation J s R a) := by
  have : (sigma J s R a).IsEquivalence := by
    rw [← P.translation_eq]
    infer_instance
  have : (sigma J s R a).Additive := by
    constructor
    intro M N f g
    ext X x
    rfl
  have : IsGrothendieckAbelian.{u} (Modules R) :=
    (SheafOfModules.grothendieckAbelian_with_localized_generator J R).1
  obtain ⟨I⟩ := Endofunctor.IsoAlgebra.exists_exactOrbitInduction (sigma J s R a)
  let P' : ModulePresentation J s R a :=
    { P with translation := (sigma J s R a).asEquivalence, translation_eq := rfl }
  exact ⟨{
    toModulePresentation := P'
    induction := I.induction
    inductionAdjunction := I.adjunction
    inductionSum := I.sum
    translationStep := I.step
    induction_shift := I.shift
    induction_zero := I.zero
    induction_add := I.add
    induction_limits := I.limits
    induction_colimits := I.colimits }⟩

/-- The semidirect ringed site, with exact orbit induction and its tensor/Hom calculus.
Stacks Tag 00W0 is motivation only. -/
theorem presentation [HasPullbacks C] : Nonempty (Presentation J s R a) := by
  obtain ⟨P⟩ := siteRestriction J s R a
  obtain ⟨M⟩ := addLimits J s R a P
  obtain ⟨I⟩ := addOrbit J s R a M
  obtain ⟨Q⟩ := closedComparisons J s R a I
  exact ⟨Q.val⟩

end CategoryTheory.TwistedActionRingedSite
