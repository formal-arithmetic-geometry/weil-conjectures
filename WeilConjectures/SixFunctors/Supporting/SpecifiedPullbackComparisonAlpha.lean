/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible

/-!
# The specified quotient-cone pullback comparison

The level maps, their strict tower, both coordinates of the Roos map, and the
zero-shifted-coordinate completion map are the existing normalized constructions.
The theorem asserts their quasi-isomorphism and identifies the completed comparison
with their localization, including all representative comparison isomorphisms.

## References

* Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1, Section 6.5, Lemma 6.5.9(4),
  Lemma 6.8.2(1)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory

namespace WeilConjectures

/-- The concrete quotient-cone model for the canonical completed pullback comparison.
Here `scalarPullbackLevel`, `scalarPullbackTower`, and `scalarPullbackChain` are
respectively the specified maps d_m, their strict tower map, and delta_P.
`integralScalarCompletionChain` is chi_Y(P), with zero shifted coordinate and
quotient projections in its other coordinate. The isomorphism e identifies an
arbitrary good representative P with K; it is not an extra restriction on K. -/
theorem specifiedPullbackComparisonAlpha
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    ∃ hF : IsSfDerivedComplete l E X ((integralDerivedPullback l E g).obj K),
      (∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ K),
        integralOperationsGoodComplex l L Y
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P.obj) ∧
        QuasiIso ((integralScalarCompletionChain l E L ι Y).app P.obj) ∧
        QuasiIso (scalarPullbackChain l E L ι g P.obj) ∧
        ((scalarCompletionIso l E L ι Y K hK.1).hom ≫
            (integralScalarExtension l E L ι Y).map e.inv ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryDerivedScalar l E L ι Y).map e.inv ≫
            (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj)) ∧
        (scalarPullbackCompleted l E L ι g K hK.1 hF).hom =
          (scalarCompletionIso l E L ι X _ hF).inv ≫
            (integralOrdinaryDerivedScalar l E L ι X).map
              ((integralDerivedPullback l E g).map e.inv) ≫
            (integralOrdinaryDerivedScalar l E L ι X).map
              ((integralDerivedPullbackComparison l E g).hom.app P) ≫
            (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
              ((integralOperationsPullbackComplexFunctor l E g).obj P.obj) ≫
            DerivedCategory.Q.map (scalarPullbackChain l E L ι g P.obj) ≫
            (integralDerivedPullbackComparison l L g).inv.app
              ⟨_, scalarGood l E L ι Y P⟩ ≫
            (integralDerivedPullback l L g).map
              ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.inv.app P.obj) ≫
            (integralDerivedPullback l L g).map
              ((integralOrdinaryDerivedScalar l E L ι Y).map e.hom) ≫
            (integralDerivedPullback l L g).map
              (scalarCompletionIso l E L ι Y K hK.1).hom) ∧
      ∀ (K' : DerivedCategory (integralTowerModules l E Y))
        (hK' : sfIntegralConstructible l E Y K')
        (hF' : IsSfDerivedComplete l E X ((integralDerivedPullback l E g).obj K'))
        (a : K ⟶ K'),
        (integralScalarExtension l E L ι X).map ((integralDerivedPullback l E g).map a) ≫
            (scalarPullbackCompleted l E L ι g K' hK'.1 hF').hom =
          (scalarPullbackCompleted l E L ι g K hK.1 hF).hom ≫
            (integralDerivedPullback l L g).map ((integralScalarExtension l E L ι Y).map a) := by
  have hF := ((integralOperations_preserve_constructible l E g).1 K hK).1.1
  refine ⟨hF, ?_, ?_⟩
  · intro P e
    have hc := (scalarCompletion_existsUnique l E L ι Y).exists.choose_spec.1 P
    change (scalarCompletion l E L ι Y).app _ ≫ _ = _ at hc
    have hp := (scalarPullbackOrdinary_existsUnique l E L ι g).exists.choose_spec P
    change _ = (scalarPullbackOrdinary l E L ι g).hom.app
      (DerivedCategory.Q.obj P.obj) ≫ _ ≫ _ at hp
    have hce :
        (scalarCompletionIso l E L ι Y K hK.1).hom ≫
            (integralScalarExtension l E L ι Y).map e.inv ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryDerivedScalar l E L ι Y).map e.inv ≫
            (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj) := by
      change (scalarCompletion l E L ι Y).app K ≫ _ ≫ _ = _
      rw [← (scalarCompletion l E L ι Y).naturality_assoc e.inv, hc]
    have hchi : IsIso
        (DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj)) := by
      have hi : IsIso
          ((integralOrdinaryDerivedScalar l E L ι Y).map e.inv ≫
            (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj)) := by
        rw [← hce]
        infer_instance
      simpa only [isIso_comp_left_iff] using hi
    have hdelta : IsIso (DerivedCategory.Q.map (scalarPullbackChain l E L ι g P.obj)) := by
      have hi : IsIso
          ((integralOrdinaryDerivedScalar l E L ι X).map
              ((integralDerivedPullbackComparison l E g).hom.app P) ≫
            (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
              ((integralOperationsPullbackComplexFunctor l E g).obj P.obj) ≫
            DerivedCategory.Q.map (scalarPullbackChain l E L ι g P.obj)) := by
        rw [hp]
        infer_instance
      simpa only [isIso_comp_left_iff] using hi
    refine ⟨scalarGood l E L ι Y P,
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hchi,
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hdelta, hce, ?_⟩
    dsimp only [scalarPullbackCompleted, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Functor.mapIso_hom]
    rw [reassoc_of% hp]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
    have he := (scalarPullbackOrdinary l E L ι g).hom.naturality e.inv
    dsimp only [Functor.comp_map] at he
    rw [reassoc_of% he]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  · intro K' hK' hF' a
    have hnX := (scalarCompletion l E L ι X).naturality
      ((integralDerivedPullback l E g).map a)
    change _ ≫ (scalarCompletionIso l E L ι X _ hF').hom =
      (scalarCompletionIso l E L ι X _ hF).hom ≫ _ at hnX
    have hx :
        (integralScalarExtension l E L ι X).map ((integralDerivedPullback l E g).map a) ≫
            (scalarCompletionIso l E L ι X _ hF').inv =
          (scalarCompletionIso l E L ι X _ hF).inv ≫
            (integralOrdinaryDerivedScalar l E L ι X).map
              ((integralDerivedPullback l E g).map a) := by
      apply (cancel_epi (scalarCompletionIso l E L ι X _ hF).hom).1
      rw [← Category.assoc, ← hnX, Category.assoc]
      simp
    dsimp only [scalarPullbackCompleted, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    rw [reassoc_of% hx]
    have ha := (scalarPullbackOrdinary l E L ι g).hom.naturality a
    dsimp only [Functor.comp_map] at ha
    rw [reassoc_of% ha]
    simp only [← Functor.map_comp]
    have hnY := (scalarCompletion l E L ι Y).naturality a
    change _ ≫ (scalarCompletionIso l E L ι Y K' hK'.1).hom =
      (scalarCompletionIso l E L ι Y K hK.1).hom ≫ _ at hnY
    rw [← hnY]

end WeilConjectures
