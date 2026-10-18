/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.CategoryTheory.TruncationHypercohomology

/-!
# Amplitude of open direct image on classical finite-coefficient sheaves

Source: blueprint main-20261015, sec-six-functors-basics,
sk-cor-geo-open-finiteness-ii/det-geo-open-finiteness-ii-amplitude.md;
Stacks Project, Tags 0F10, 0D6J and 09A6
(blueprint: det-geo-open-finiteness-ii-amplitude).

Fixed-ring module sheaves present modules over the specified coefficient ring sheaves,
via `finiteCoefficientEtaleRealization` and `finiteCoefficientRealization`. The comparison
is the recorded inverse image of `proEtaleSiteComparisonModules`. The derived images here
are its exact derived functor followed by the bounded below right derived direct image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- An open immersion of finite-type schemes over a field has finite torsion etale
cohomological dimension, bounds higher etale and classical pro-etale images of module
sheaves by that dimension, and sends the cohomological interval `[a,b]` to `[a,b+d]`.
The existential natural number is exactly the recorded dimension, so it asserts its
finiteness, rather than merely choosing an unspecified upper bound.
Source: blueprint main-20261015, det-geo-open-finiteness-ii-amplitude, clauses (1)-(3);
Stacks Project, Tags 0F10, 0D6J and 09A6
(blueprint: det-geo-open-finiteness-ii-amplitude).

Proof:
1. Finite-type schemes over a field are Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Their opens are quasi-compact by
   lem-weil-pbc-noetherian-open-subscheme-noetherian. Thus X, Y and j are qcqs.
   Apply lem-kun-0f10 to get finite cd(j); def-kun-cd gives its natural-number value d,
   including the empty source case.
2. The ring-sheaf module categories are Grothendieck by
   lem-weil-pbc-ring-sheaves-grothendieck. Functorial injective embeddings and
   lem-weil-pbc-dplus-injective-representative give injective resolutions, starting in
   degree zero for sheaves. The K-injective computation is def-sfb-right-derived-functor.
   Underived direct image evaluates on fibre products. Exact forgetting of scalars
   (lem-weil-pbc-module-sheaves-colimits-forgetful) commutes with cohomology and reflects
   zero objects; no commutativity of the coefficient ring is used.
3. For a module injective I, the ringed-site evaluation comparison
   lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison and injective acyclicity
   from lemma-weil-pbc-leray-acyclicity show positive abelian section cohomology vanishes.
   By lem-weil-pbc-higher-direct-image-sheafified-presheaf the forgotten I is acyclic for
   abelian direct image. The acyclic-resolution criterion of Leray therefore identifies
   module higher images with abelian higher images after forgetting. This does not
   assume forgetting preserves injectives. The degree-zero resolutions also give
   negative-degree vanishing.
4. Every module sheaf is torsion after forgetting: the stipulated power annihilates it;
   alternatively a positive additive exponent of the finite ring annihilates all
   modules. The defining bound def-kun-cd and step 3 give clause (1).
5. The canonical qcqs comparison prop-weil-pbc-comparison-direct-image identifies the
   pro-etale image of the comparison pullback with the comparison pullback of the
   etale image. Exactness from prop-weil-pbc-site-comparison-finite-level commutes with
   kernels, images and cokernels, hence cohomology. Step 4 gives clause (2), and step 3
   supplies its lower bound zero.
6. Apply thm-sp-truncation-e2 to etale direct image and M. Its convergent truncation
   spectral sequence has E2 terms R^p j_* H^q(M), zero outside 0 <= p <= d and
   a <= q <= b. For n outside [a,b+d] every associated graded object of the finite
   exhaustive separated abutment filtration is zero. Successive equality of its terms
   identifies the whole abutment with its zero end term. Apply step 5 to M to obtain
   clause (3). This includes a > b, missing cohomology degrees, and the zero complex;
   no constructibility, separatedness over k or invertibility in k is required. -/
theorem openDirectImage_classical_amplitude
    (k : Type u) [Field k] (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (ℓ : ℕ) (hΛ : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : Λ, (ℓ ^ r) • x = 0)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : X ⟶ Y) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] :
    ∃ d : ℕ,
      (@Scheme.Hom.torsionEtaleCohomologicalDimension _ _ j
        (@quasiCompact_of_compactSpace X Y j
          ((quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance)
          (@IsLocallyNoetherian.quasiSeparatedSpace Y
            (LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k)))))
        (@QuasiSeparated.of_quasiSeparatedSpace X Y j
          (@IsLocallyNoetherian.quasiSeparatedSpace X
            (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)))))) = (d : ℕ∞) ∧
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ),
        (d : ℤ) < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
            ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) j).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F)))) ∧
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ),
        (d : ℤ) < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) q).obj
            ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
              ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F))))) ∧
      (∀ (a b : ℤ)
        (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        (∀ q : ℤ, (q < a ∨ b < q) →
          IsZero ((DerivedCategory.Plus.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj M)) →
        ∀ q : ℤ, (q < a ∨ b + (d : ℤ) < q) →
          IsZero ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) q).obj
              ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
                ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj M)))) :=
  sorry

end AlgebraicGeometry.ProEtale
