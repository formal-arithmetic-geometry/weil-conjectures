/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# Bounded constructible derived comparison for arbitrary finite rings

Source: Stacks Project, Tag 09AL, lemma-compare-constructible-derived, and its exact
cohomology comparison, with the blueprint's global finite-stratification convention
(blueprint: lem-weil-pbc-finite-ring-constructible-derived-origin).

The induced equivalence is stated by its equivalent full-faithfulness and essential-image
criterion. The functor is the specified exact inverse image, in the canonical constant-ring
presentation used by intrinsic constructibility. Its source is the existing full bounded
constructible etale subcategory. The essential-image criterion includes the etale-origin
conclusion, without choosing an inverse equivalence.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def intrinsicRealizationRestrictionIso (X : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B]
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) :
    (ProEtale.finiteCoefficientIntrinsicRealization X B).obj
      ((proEtaleModuleRestriction X B).obj M) ≅ M :=
  asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap X B)).counit.app M)

private theorem intrinsicRealization_constructible_iff (X : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B]
    (G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    IsConstructibleProEtaleModuleSheaf X B
      ((ProEtale.finiteCoefficientIntrinsicRealization X B).obj G) ↔
        ProEtale.IsConstructible (ULift.{u + 1, u} B) G := by
  let R := ProEtale.finiteCoefficientIntrinsicRealization X B
  have : R.IsEquivalence :=
    (ProEtale.finiteCoefficientIntrinsicRealization_exact X B).1
  let e : (proEtaleModuleRestriction X B).obj (R.obj G) ≅ G :=
    R.preimageIso (intrinsicRealizationRestrictionIso X B (R.obj G))
  rw [proEtaleModuleRestriction_constructible_iff]
  exact ⟨fun h ↦ ProEtale.isConstructible_of_iso e h,
    fun h ↦ ProEtale.isConstructible_of_iso e.symm h⟩

private theorem intrinsicConstructible_of_iso (X : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B]
    {M N : proEtaleRingModules X (proEtaleConstantRing X B)} (e : M ≅ N)
    (h : IsConstructibleProEtaleModuleSheaf X B M) :
    IsConstructibleProEtaleModuleSheaf X B N := by
  rw [proEtaleModuleRestriction_constructible_iff] at h ⊢
  exact ProEtale.isConstructible_of_iso ((proEtaleModuleRestriction X B).mapIso e) h

end AlgebraicGeometry.Scheme
