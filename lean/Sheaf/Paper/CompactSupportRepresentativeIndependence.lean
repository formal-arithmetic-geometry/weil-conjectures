/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.Compactification.CategoryBaseChange
import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.SfIntegralConstructibleLinear
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-!
# Compact support and specified rational identifications

Source: Weil blueprint, sec-smooth-purity/sk-def-sf-operations, order 1494;
main-20261015, sec-six-functors-basics/sk-thm-sf-pf-field, order 1853
(blueprint: lem-weil-compact-support-representative-independence).

The comparison is a single simultaneous family indexed by specified input
isomorphisms, realized by the scalar extension of an integral linear functor with
the prescribed compact-support values. The integral functor is naturally identified
with the coherent strict tower followed by total derived inverse limit; that comparison
preserves the projections of the chosen Roos vertex. Its tensor-Hom formula fixes
the rational extension.
The presentation clause records its cocycle for a common rational
object. It does not assert uniqueness of an isomorphism between bare objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct

namespace WeilConjectures

/-- Specified rational identifications induce coherent compact-support comparisons.
The compactification c is fixed at every finite coefficient level, exactly as in
sfIntegralCompactSupportValue. The index of each reduction is the positive exponent n+1.
Source: Weil blueprint, order 1494, and main-20261015, order 1853
(blueprint: lem-weil-compact-support-representative-independence).

Proof (the five steps of the DAG):
1. Compactifications exist by prop-compactification-refinement under the field,
finite-type and separated hypotheses. Fix c and use the small pro-etale sites of
 def-weil-pbc-proetale-site. Apply lem-weil-compact-support-reduction-tower-functor
 to obtain the exact coherent strict tower T with its natural evaluation comparisons
 and prescribed quotient transitions. Apply lem-weil-pbc-ringed-strict-tower-homotopy-limit
 to obtain the genuine functor L = Rlim. Resolve the entire strict tower, rather than
 its unrelated evaluations. The exact composite L T computes integral compact support.
2. Multiplication by compatible constant sections gives the integral scalar action
 of lem-weil-integral-constructible-linear, componentwise on strict towers. Their
 category is abelian by lem-weil-tower-category-levelwise-abelian. The localization
 and shifts are linear by lem-weil-linear-abelian-derived-category. On K-injective
 tower representatives, lem-weil-pbc-kinjective-hom-derived identifies each derived
 Hom with the homotopy Hom. Conjugate a derived map by its resolution isomorphisms.
 The representatives of a h and h+h' are a times the representative of h and the
 sum of the representatives, respectively, by bijectivity of that Hom map.
 Termwise limit preserves these identities and chain homotopies. Target localization
 is linear, so L and L T are linear without a linear choice of resolution functor.
3. Apply lem-sf-integral-compact-support-constructible to the same c and transitions.
 The values lie in the integral constructible category, with one common interval
 for all reductions. Restrict L T to this full subcategory; the inherited structures
 of lem-weil-integral-constructible-triangulated and
 lem-weil-integral-constructible-linear preserve exactness and linearity. Identify
 its values with sfIntegralCompactSupportValue, transporting along the fixed
 comparisons to the chosen derived-limit vertices in that definition. Choose T and
 its evaluation isomorphisms e from exists_compactSupportReductionTower and RF and η
 from ringedStrictTowerHomotopyLimitOfUniverses. The derived projections π are normalized
 by η against the ordinary limit projections on complexes, using the exact-evaluation
 factorization. The natural isomorphism γ from the inclusion of F to T followed by RF
 carries these projections, via e n, to the projections chosen in the derived-limit
 witness defining sfIntegralCompactSupportValue. This fixes the map transport as well
 as the object values.
4. Extend this integral functor on the raw tensor Hom groups of
 def-weil-rationalization-karoubi and def-weil-linear-scalar-localization by
 u tensor e mapping to F(u) tensor e. The tensor balancing of
 def-weil-module-base-change follows from integral linearity. Functoriality follows
 on pure tensors from F(vu)=F(v)F(u) and F(1)=1, then on sums by bilinearity.
 Any linear extension has that pure-tensor formula, so the extension is unique
 for the fixed integral functor. Its object values are sfRationalCompactSupportValue.
5. Take beta(alpha) to be the image of alpha, with inverse the image of its inverse.
 The functor laws give the identity and composition clauses. For presentations
 a and a' of M the input is a followed by the inverse of a', hence the comparison
 is beta(a followed by inverse a'). Cancelling the middle presentation gives the
 final cocycle. No choice-independent comparison of bare isomorphism classes is used. -/
theorem exists_compactSupportRepresentativeComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    (X Y : Scheme.{u})
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (fun [hproducts : HasCountableProducts
        (DerivedCategory (scalarReductionSource l E Y))] ↦
    ∃ (T : DerivedCategory (scalarReductionSource l E X) ⥤
        DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)))
      (e : ∀ n : ℕ,
        T ⋙ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
          compactSupportRestrictedLevel l E c n),
      T = Classical.choose (Classical.choose_spec (Classical.choose_spec
            (exists_compactSupportReductionTower l E K₀ X Y f hl c))).2.2 ∧
      HEq e (Classical.choose (Classical.choose_spec
          (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
            (exists_compactSupportReductionTower l E K₀ X Y f hl c))).2.2).2).2) ∧
      ∃ (RF : DerivedCategory
          (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) ⥤
            DerivedCategory (scalarReductionSource l E Y))
        (η : (lim : pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y) ⥤
            scalarReductionSource l E Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF),
        RF = Classical.choose
          (@ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u + 1}
            Y.ProEt inferInstance (ProEt.topology Y) inferInstance inferInstance
            ((adicLisseForget Y).obj (completedIntegralCommRingSheafUnrestricted l E Y))
            (fun U a b ↦ @mul_comm
              ((completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) inferInstance a b)
            (scalarReductionSourceDerived l E Y)
            (pbcTowers_hasDerivedCategory Y (completedIntegralCommRingSheafUnrestricted l E Y))) ∧
        HEq η (Classical.choose (Classical.choose_spec
          (@ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u + 1}
            Y.ProEt inferInstance (ProEt.topology Y) inferInstance inferInstance
            ((adicLisseForget Y).obj (completedIntegralCommRingSheafUnrestricted l E Y))
            (fun U a b ↦ @mul_comm
              ((completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) inferInstance a b)
            (scalarReductionSourceDerived l E Y)
            (pbcTowers_hasDerivedCategory Y (completedIntegralCommRingSheafUnrestricted l E Y))))) ∧
        ∃ π : ∀ n : ℕ,
            RF ⟶ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n,
          (∀ (n : ℕ)
            (I : CochainComplex
              (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) ℤ),
            η.app I ≫ (π n).app (DerivedCategory.Q.obj I) ≫
                (Functor.mapDerivedCategoryFactors
                  ((evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n))).hom.app I =
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app I)) ∧
          ∃ F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y,
      F.Additive ∧ F.Linear (Padic.coefficientExtensionIntegers l E) ∧
      (∀ K : sfIntegralConstructibleCategory l E X,
        F.obj K = sfIntegralCompactSupportValue l E K₀ hl c K) ∧
      (∃ γ : F ⋙ (sfIntegralConstructible l E Y).ι ≅
          (sfIntegralConstructible l E X).ι ⋙ T ⋙ RF,
        ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
          HEq (γ.hom.app K ≫ (π n).app (T.obj K.obj) ≫ (e n).hom.app K.obj)
            (Classical.choose (Classical.choose_spec
                (exists_isDerivedLimit_and_iso
                  (sfCompactSupportTerm l E c K.obj)
                  (sfCompactSupportTransition l E c K.obj)).1) ≫
              Pi.π (sfCompactSupportTerm l E c K.obj) n)) ∧
      ∃ G : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y,
        G.Linear (Localization.Away (Padic.coefficientExtensionUniformizer l E)) ∧
        (∀ K : sfIntegralConstructibleCategory l E X,
          G.obj ((sfRationalConstructibleLocalization l E X).obj K) =
            sfRationalCompactSupportValue l E K₀ hl c K) ∧
        (∀ (K K' : sfIntegralConstructibleCategory l E X) (v : K ⟶ K')
          (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
          HEq (G.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] v :
            (sfRationalConstructibleLocalization l E X).obj K ⟶
              (sfRationalConstructibleLocalization l E X).obj K'))
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] F.map v :
              (sfRationalConstructibleLocalization l E Y).obj (F.obj K) ⟶
                (sfRationalConstructibleLocalization l E Y).obj (F.obj K'))) ∧
        ∃ beta : ∀ (K K' : sfIntegralConstructibleCategory l E X),
        ((sfRationalConstructibleLocalization l E X).obj K ≅
          (sfRationalConstructibleLocalization l E X).obj K') →
        (sfRationalCompactSupportValue l E K₀ hl c K ≅
          sfRationalCompactSupportValue l E K₀ hl c K'),
      (∀ (K K' : sfIntegralConstructibleCategory l E X)
        (alpha : (sfRationalConstructibleLocalization l E X).obj K ≅
          (sfRationalConstructibleLocalization l E X).obj K'),
        HEq (beta K K' alpha) (G.mapIso alpha)) ∧
      (∀ K : sfIntegralConstructibleCategory l E X,
        beta K K (Iso.refl _) = Iso.refl _) ∧
      (∀ (K K' K'' : sfIntegralConstructibleCategory l E X)
        (alpha : (sfRationalConstructibleLocalization l E X).obj K ≅
          (sfRationalConstructibleLocalization l E X).obj K')
        (alpha' : (sfRationalConstructibleLocalization l E X).obj K' ≅
          (sfRationalConstructibleLocalization l E X).obj K''),
        beta K K'' (alpha ≪≫ alpha') = beta K K' alpha ≪≫ beta K' K'' alpha') ∧
      (∀ (M : sfRationalConstructibleCategory l E X)
        (K K' K'' : sfIntegralConstructibleCategory l E X)
        (a : (sfRationalConstructibleLocalization l E X).obj K ≅ M)
        (a' : (sfRationalConstructibleLocalization l E X).obj K' ≅ M)
        (a'' : (sfRationalConstructibleLocalization l E X).obj K'' ≅ M),
        beta K K' (a ≪≫ a'.symm) ≪≫ beta K' K'' (a' ≪≫ a''.symm) =
          beta K K'' (a ≪≫ a''.symm)))
      (hproducts := integralOperationsDerivedCountableProducts l E Y) := by
  sorry

end WeilConjectures
