/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical finite-coefficient derived model comparisons

Source: Stacks Project, Sites, Tags 00YV and 0H7J; Derived Categories, Tag 015F;
Categories, Tag 04VG; blueprint comparison-pullback, final sentence on complexes;
`FiniteFieldStratifiedPerfectModels.lean`, the three comparison constructions
(blueprint: lem-weil-pbc-finite-coefficient-derived-model-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Finite-coefficient realization commutes canonically with scheme inverse image and
with arbitrary termwise constant cochain complexes. The first equality specifies unit
cancellation before the canonical site comparison; the second specifies its exact
localization. The last equality specifies the constant comparison through the exact
localization factors and the degreewise constant-module isomorphism. Thus the two
comparisons are natural on the entire derived category and on all chain maps,
respectively, rather than only isomorphisms of cohomology groups or graded objects.

Source: Stacks Project, Tags 00YV, 0H7J, 015F and 04VG; blueprint comparison-pullback,
last sentence; the three comparison constructions in FiniteFieldStratifiedPerfectModels
(blueprint: lem-weil-pbc-finite-coefficient-derived-model-comparison).

Proof:
1. The coefficient realization is the recorded exact equivalence. Comparison and
scheme inverse images are geometric inverse images: etale base change preserves
coverings, fibre products and the terminal object (etale-base-change-continuous and
left-exact-site-inverse-image-tensor). Constant-left-module-inverse-image therefore
makes the fixed-ring module inverse images exact. Exact-functor-derived-factorization
applies to their unbounded cochain complexes, without resolutions or bounds.
2. Cancel the inverse-realization/realization pair by the inverse unit of the specified
coefficient equivalence. Whisker the canonical comparison-pullback isomorphism with
realization. These give the displayed module-functor isomorphism b, natural in all
etale module sheaves.
3. Descend b with exact-derived-natural-iso and use exact-derived-composition on its
two sides. Their localization normalizations identify beta with the termwise b on
every localized complex, and localization gives naturality on all derived inputs.
4. Geometric-inverse-image-constant-module gives the canonical constant comparison,
natural in every linear map. Its square at each differential P.d q (q+1) is the
chain-map equation; applying the inverse components gives its inverse chain map.
Its square at every component of a chain map gives naturality for all cochain maps.
This is precisely mapHomologicalComplexCompIso of comparisonUpperStarConstantSheafIso.
5. Apply the composition comparison, then realization of the exact localization
factor for nu, then realization of the localization of the chain isomorphism from
step 4. Each factor is natural, yielding gamma and the displayed component formula.
All integer degrees, zero terms, infinite modules and unbounded complexes are allowed.
-/
theorem finite_coefficient_derived_model_comparison
    (B : Type (u + 1)) [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B] {U X : Scheme.{u}} (f : U ⟶ X) :
    ∃ b : finiteCoefficientComparison X B ⋙ finiteCoefficientPullback X B f ≅
        Etale.upperStar (ModuleCat.{u + 1} B) f ⋙ finiteCoefficientComparison U B,
      b =
        Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} B) X)
          (Functor.isoWhiskerRight (finiteCoefficientRealization X B).asEquivalence.unitIso.symm
            (upperStar (ModuleCat.{u + 1} B) f ⋙ finiteCoefficientRealization U B)) ≪≫
          Functor.isoWhiskerRight
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f)
            (finiteCoefficientRealization U B) ∧
      ∃ beta : finiteCoefficientDerivedComparison X B ⋙
          finiteCoefficientDerivedPullback X B f ≅
            (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory ⋙
              finiteCoefficientDerivedComparison U B,
        beta = (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryNatIso b ≪≫ Functor.mapDerivedCategoryCompIso _ _ ∧
        ∀ T : Scheme.{u}, ∃ gamma :
          (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙ finiteCoefficientDerivedComparison T B ≅
            (constantSheaf (Scheme.ProEt.topology T)
                (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q ⋙ (finiteCoefficientRealization T B).mapDerivedCategory,
          ∀ P : CochainComplex (ModuleCat.{u + 1} B) ℤ,
            gamma.app P =
              (Functor.mapDerivedCategoryCompIso
                (comparisonUpperStar (ModuleCat.{u + 1} B) T)
                (finiteCoefficientRealization T B)).app
                  (DerivedCategory.Q.obj
                    (((constantSheaf T.smallEtaleTopology
                      (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≪≫
                (finiteCoefficientRealization T B).mapDerivedCategory.mapIso
                  ((comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategoryFactors.app
                    (((constantSheaf T.smallEtaleTopology
                      (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
                    DerivedCategory.Q.mapIso
                      ((Functor.mapHomologicalComplexCompIso
                        (comparisonUpperStarConstantSheafIso B T) (ComplexShape.up ℤ)).app P)) := by
  refine ⟨_, rfl, _, rfl, ?_⟩
  intro T
  let C : CochainComplex (ModuleCat.{u + 1} B) ℤ ⥤
      CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
    (constantSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)
  let N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B) :=
    comparisonUpperStar (ModuleCat.{u + 1} B) T
  let E : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)) ⥤
      FiniteCoefficientDerivedCategory T B := (finiteCoefficientRealization T B).mapDerivedCategory
  let k : C ⋙ N.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso
      (comparisonUpperStarConstantSheafIso B T) (ComplexShape.up ℤ)
  refine ⟨Functor.isoWhiskerLeft (C ⋙ DerivedCategory.Q)
      (Functor.mapDerivedCategoryCompIso N (finiteCoefficientRealization T B)) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft C N.mapDerivedCategoryFactors) E ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight k DerivedCategory.Q) E, ?_⟩
  intro P
  apply Iso.ext
  simp only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Functor.map_comp]
  rfl

end AlgebraicGeometry.ProEtale
