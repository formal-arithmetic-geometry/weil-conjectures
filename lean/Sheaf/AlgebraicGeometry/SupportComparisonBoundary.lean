/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.AlgebraicGeometry.SupportComparisonBoundaryMaps

import Sheaf.AlgebraicGeometry.SiteNormalizedSupportSequence
import Sheaf.AlgebraicGeometry.SupportComparisonInjectiveLadder
import Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit

/-! # Site-comparison compatibility of the support boundary

Source: Stacks Project, etale-cohomology.tex Tag 09XP and homology.tex Tag 0117
(blueprint: lem-pur-support-comparison-boundary).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Canonical etale/pro-etale support comparison preserves the normalized boundary.
Source: Stacks Project Tag 09XP and (blueprint: lem-pur-support-comparison-boundary).

Proof: restriction along the open complement is surjective on injective
module sheaves, by the free-module Yoneda monomorphism and injectivity.
Apply the normalized derived connecting-map construction to obtain both exact
support sequences. The ordinary comparison pullback mate identifies the units
on the open complement. Choose injective models of F and of its comparison
inverse image and lift the derived comparison identification to a chain map.
The ordinary comparison units and this map give a morphism of short exact
support complexes realizing all three prescribed comparison maps. Transport
snake-boundary naturality and the two other homology squares through these
models. Naturality in F is that of the three prescribed natural transformations;
all arrows are morphisms of A-modules. -/
theorem exists_support_comparison_boundary
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (C : Scheme.{u}) (i : C ⟶ T) [IsClosedImmersion i] :
    ∃ (δₑ : Sheaf.SupportSequenceBoundary T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) ⊤)
      (δₚ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) ⊤),
      ProEtale.SupportBoundaryOpenUnitNormalized A i.openComplement.ι ∧
      supportBoundaryNormalization T.smallEtaleTopology A
        (Etale.supportRestrictionArrow i) δₑ ∧
      supportBoundaryNormalization (Scheme.ProEt.topology T) A
        (ProEtale.supportRestrictionArrow i) δₚ ∧
      Sheaf.SupportSequenceExact T.smallEtaleTopology (ModuleCat.{u + 1} A)
        (Etale.supportRestrictionArrow i) ⊤ δₑ ∧
      Sheaf.SupportSequenceExact (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
        (ProEtale.supportRestrictionArrow i) ⊤ δₚ ∧
      (∀ (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (δₑ q).app ⟨(DerivedCategory.Plus.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F, trivial⟩ ≫
            (ProEtale.supportComparisonHypercohomology A i (q + 1)).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) =
          (ProEtale.finiteComparisonSectionHypercohomology T A
              (Scheme.Etale.mk i.openComplement.ι) q).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
            (δₚ q).app ⟨(DerivedCategory.Plus.singleFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).obj F,
              trivial⟩) ∧
      (∀ (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (Sheaf.supportHypercohomologyInclusion T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) q).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
            (ProEtale.finiteComparisonGlobalHypercohomology T A q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) =
          (ProEtale.supportComparisonHypercohomology A i q).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.supportHypercohomologyInclusion (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) q).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).obj F)) ∧
      (∀ (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (Sheaf.sectionHypercohomologyRestriction T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) q).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
            (ProEtale.finiteComparisonSectionHypercohomology T A
              (Scheme.Etale.mk i.openComplement.ι) q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) =
          (ProEtale.finiteComparisonGlobalHypercohomology T A q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.sectionHypercohomologyRestriction (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) q).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).obj F)) ∧
      (∀ (q : ℤ) (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
          (f : F ⟶ G),
        (Sheaf.supportHypercohomologyFunctor T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map f) ≫
            (ProEtale.supportComparisonHypercohomology A i q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj G) =
          (ProEtale.supportComparisonHypercohomology A i q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).map f)) ∧
      (∀ (q : ℤ) (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
          (f : F ⟶ G),
        (Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Scheme.Etale.mk (𝟙 T)) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map f) ≫
            (ProEtale.finiteComparisonGlobalHypercohomology T A q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj G) =
          (ProEtale.finiteComparisonGlobalHypercohomology T A q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (Scheme.ProEt.mk (𝟙 T)) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).map f)) ∧
      (∀ (q : ℤ) (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
          (f : F ⟶ G),
        (Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Scheme.Etale.mk i.openComplement.ι) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map f) ≫
            (ProEtale.finiteComparisonSectionHypercohomology T A
              (Scheme.Etale.mk i.openComplement.ι) q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj G) =
          (ProEtale.finiteComparisonSectionHypercohomology T A
              (Scheme.Etale.mk i.openComplement.ι) q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (Scheme.ProEt.mk i.openComplement.ι) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).map f)) := by
  let : Mono (Etale.supportRestrictionArrow i) := ⟨fun f g h ↦ by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono i.openComplement.ι).mp
    exact congrArg (fun t ↦ t.left) h⟩
  let : Mono (ProEtale.supportRestrictionArrow i) := ⟨fun f g h ↦ by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono i.openComplement.ι).mp
    exact congrArg (fun t ↦ t.left) h⟩
  obtain ⟨δₑ, hₑ, eₑ⟩ := exists_site_normalized_support_sequence
    T.smallEtaleTopology A (Etale.supportRestrictionArrow i)
  obtain ⟨δₚ, hₚ, eₚ⟩ := exists_site_normalized_support_sequence
    (Scheme.ProEt.topology T) A (ProEtale.supportRestrictionArrow i)
  have hunit : ProEtale.SupportBoundaryOpenUnitNormalized A i.openComplement.ι := by
    intro F
    have h := ProEtale.comparisonPullbackOpenUnit A i.openComplement.ι F
    change _ ≫ (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) _).map
      ((ProEtale.supportBoundaryOpenCoefficientIso A i.openComplement.ι).inv.app F) = _ at h
    have h' := congrArg
      (fun t ↦ t ≫ (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) _).map
        ((ProEtale.supportBoundaryOpenCoefficientIso A i.openComplement.ι).hom.app F)) h
    simpa [Category.assoc, ← Functor.map_comp] using h'
  refine ⟨δₑ, δₚ, hunit, hₑ, hₚ, eₑ, eₚ,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q F
    obtain ⟨M⟩ := exists_supportComparison_injective_ladder k A T C i δₑ δₚ hₑ hₚ F
    exact M.δ_naturality q
  · intro q F
    obtain ⟨M⟩ := exists_supportComparison_injective_ladder k A T C i δₑ δₚ hₑ hₚ F
    exact M.f_naturality q
  · intro q F
    obtain ⟨M⟩ := exists_supportComparison_injective_ladder k A T C i δₑ δₚ hₑ hₚ F
    exact M.g_naturality q
  · intro q F G f
    exact (ProEtale.supportComparisonHypercohomology A i q).naturality
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map f)
  · intro q F G f
    exact (ProEtale.finiteComparisonGlobalHypercohomology T A q).naturality
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map f)
  · intro q F G f
    exact (ProEtale.finiteComparisonSectionHypercohomology T A
      (Scheme.Etale.mk i.openComplement.ι) q).naturality
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map f)

end AlgebraicGeometry
