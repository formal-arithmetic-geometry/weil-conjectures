/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonClassical
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonLocal
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Constructible comparison for discrete Noetherian coefficients

We use the recorded equivalent coefficient-sized sites and intrinsic modules over their
constant ring sheaves. The two full subcategories have all ambient morphisms. The forward
functors are identified with the canonical comparison inverse image, including its
localization on complexes; an arbitrary equivalence of categories would not suffice.

## References

* Stacks Project, Tags 09AJ, 09AK and 09AL

## Main definitions

- `constructibleComparisonRingMap`: the canonical constant-section coefficient map.
- `constructibleComparisonPullback`: the module comparison inverse image.
- `constructibleComparisonComplexPullback`: its termwise action on cochain complexes.

## Main statements

- `constructibleComparison`: local constructibility, classicality and both equivalences.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Constructibility is local finite stratification with finite-type constant models.
On qcqs schemes every such module is classical, and comparison induces equivalences on
constructible sheaves and on bounded constructible derived categories.
(Stacks, Tags 09AJ, 09AK and 09AL) -/
theorem constructibleComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    (∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F ↔
        ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          ∃ S : Scheme.Stratification U.toScheme,
            (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
            ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
              (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain a)) A
              ((Scheme.coefficientProEtaleFixedModulePullback.{u, v}
                (S.immersion a ≫ U.ι) A).obj
                  ((coefficientModelFixedScalars _ A).obj F))) ∧
    (∀ [CompactSpace X] [QuasiSeparatedSpace X],
      (∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
        Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F →
          ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
            (P : AffinePresentation X I),
            IsIso (continuityMap P
              ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
                ((coefficientModelFixedScalars _ A).obj F).obj))) ∧
      (∃ e : Scheme.CoefficientConstructibleEtaleModuleCategory.{u, v} X A ≌
          ObjectProperty.FullSubcategory
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A),
        Nonempty (e.functor ⋙
          ObjectProperty.ι
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A) ≅
            ObjectProperty.ι (Scheme.IsCoefficientConstructibleEtaleModule X A) ⋙
              constructibleComparisonPullback X A)) ∧
      (∃ D : ConstantCompletion.D (ConstantCompletion.constant
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
            ConstantCompletion.D (ConstantCompletion.constant
              (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
        Nonempty (ConstantCompletion.Q _ ⋙ D ≅
          constructibleComparisonComplexPullback X A ⋙
            ConstantCompletion.Q _) ∧
        ∃ e : Scheme.CoefficientBoundedConstructibleEtaleCategory.{u, v} X A ≌
            (coefficientBoundedConstructibleProEtale X A).FullSubcategory,
          Nonempty (e.functor ⋙ (coefficientBoundedConstructibleProEtale X A).ι ≅
            ObjectProperty.ι (Scheme.IsCoefficientBoundedConstructibleEtale X A) ⋙ D))) := by
  constructor
  · intro F
    exact constructibleComparison_local X A F
  · intro _ _
    refine ⟨constructibleComparison_classical X A, ?_, ?_⟩
    · exact constructibleComparison_moduleEquivalence X A
    · obtain ⟨D, hD, hH, _⟩ := constructibleComparison_derivedFunctor X A
      exact ⟨D, hD, constructibleComparison_boundedRestriction X A D hD hH⟩

end AlgebraicGeometry.ProEtale
