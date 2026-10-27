/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # Comparison of tensor evaluation into the coefficient unit

The tensor comparison and the coefficient-unit comparison are the canonical maps
on the ordinary derived categories, with no exceptional functor involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Comparison carries evaluation into the coefficient unit to the same evaluation.
Source: Stacks sites-cohomology.tex, lemma-pullback-tensor-product (Tag 07A4),
its K-flat-model proof; sites-modules.tex, lemma-tensor-product-pullback;
lem-pur-bounded-site-tensor-transposes, proof Step 2.
(blueprint: lem-pur-site-tensor-unit-evaluation).

Proof: represent both inputs by K-flat complexes. Exact comparison preserves these
models and their tensor products. On the direct-sum total tensor, its tensor comparison
is the ordinary sheaf tensor comparison on every summand. Naturality for e therefore
moves comparison of e through the tensor comparison. The coefficient unit is the
constant rank-one complex in degree zero. On each total-tensor summand its canonical
comparison followed by the pro-etale left unitor is the image of the etale left unitor,
since both maps send a pure tensor a tensor k to a k. This proves the equation on
K-flat models. The localization defining derived tensor and the characterizing square
of leftDerivedTensorComparison descend this equation to the displayed derived maps.
This applies to zero inputs and the zero ring as well; no projection is inverted. -/
theorem siteTensorUnitEvaluation
    (A : Type (u + 1)) [CommRing A] [Finite A] (Y : Scheme.{u})
    (Q K : Etale.DerivedCategoryModule A Y) (e : Q ⟶ 𝟙_ _) :
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) Q).hom.app K) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map e ≫
            (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom)).app
              (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) ≫
        (λ_ (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K)).hom =
      D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map e).app K ≫ (λ_ K).hom) := by
  sorry

end AlgebraicGeometry.ProEtale
