/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D6
-/
module

public import Sheaf.Paper.IntegralSupportNormalizationData

/-! # Closed support comparison and normalized restricted adjunction

Source: smooth-purity localization support paragraphs; Stacks 03DI, 0GL1, 0A07
(blueprint: lem-sf-closed-support-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The closed part of support normalization, with the original maps and shifts.
Source: smooth-purity localization, integral and rational support paragraphs
(blueprint: lem-sf-closed-support-normalization). -/
structure ClosedSupport (D : FiniteFieldDatum.{u}) (primeUnit : IsUnit (l : D.k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [i.IsOver (Spec (.of D.k))] [j.IsOver (Spec (.of D.k))] where
  closed : SfOrdinaryIntegralComparison l E i
  [closedReductionIso : IsIso (closedReduction l E i closed)]
  [closedModuleColimits : PreservesFiniteColimits (sfCompletedModuleDirectImage l E i)]
  [closedModuleLimits : PreservesFiniteLimits (sfCompletedModuleDirectImage l E i)]
  di : (sfIntegralConstructible l E Z).ι ⋙ FrobeniusExchange.integralDirectImage l E i ≅
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i
  di_formula : di.inv = closedAlpha l E i closed
  closedComplete : ∀ K : DerivedCategory (scalarReductionSource l E Z),
    IsSfDerivedComplete l E Z K →
      IsSfDerivedComplete l E X ((sfCompletedDerivedDirectImage l E i).obj K)
  closedInterval : ∀ (K : sfIntegralConstructibleCategory l E Z) (a b : ℤ),
    IntegralImmersionNormalization.HasReductionInterval l E Z K.obj a b →
    IntegralImmersionNormalization.HasReductionInterval l E X
      ((sfCompletedDerivedDirectImage l E i).obj K.obj) a b
  closedProjection : ∀ (K : sfIntegralConstructibleCategory l E Z) (n : ℕ),
    di.inv.app K ≫
      (coefficientSequenceProjection l E X n).app
        ((FrobeniusExchange.systemDirect l E i).obj
          ((FrobeniusExchange.reduction l E Z).obj K.obj)) =
    (sfCompletedDerivedDirectImage l E i).map
      (((FrobeniusExchange.models l E).system Z).adjunction.unit.app K.obj ≫
        (coefficientSequenceProjection l E Z n).app
          ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
      (sfDerivedRestrictionComparison l E i n).hom.app
        ((coefficientSequenceDerivedEvaluation l E Z n).obj
          ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
      (scalarReductionDerivedRestriction l E X n).map
        ((directEvaluationIso l E i n).inv.app
          ((FrobeniusExchange.reduction l E Z).obj K.obj))
  closedReductionComparison : ∀ (K : sfIntegralConstructibleCategory l E Z) (n : ℕ),
    IsIso (sfOrdinaryPushReduction l E i K.obj n)
  [closedShift : (FrobeniusExchange.directImageFunctor l E D.k primeUnit i).CommShift ℤ]
  closedShiftNormalization : NatTrans.CommShift di.hom ℤ
  closedShiftInclusion : ∀ (n : ℤ) (M : sfIntegralConstructibleCategory l E Z),
    (((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).commShiftIso n).hom.app
      M).hom ≫ ((sfIntegralConstructible l E X).ι.commShiftIso n).hom.app
        ((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).obj M) =
      (FrobeniusExchange.integralDirectImage l E i).map
        (((sfIntegralConstructible l E Z).ι.commShiftIso n).hom.app M) ≫
      ((FrobeniusExchange.integralDirectImage l E i).commShiftIso n).hom.app M.obj
  closedTermwiseShift : NatTrans.CommShift
    (isoWhiskerLeft (sfIntegralConstructible l E Z).ι
      (sfCompletedModuleDirectImage l E i).rightDerivedFunctorIsoMapDerivedCategory).hom ℤ
  closedExact : (FrobeniusExchange.directImageFunctor l E D.k primeUnit i).IsTriangulated
  disjoint : ∀ M : sfIntegralConstructibleCategory l E Z,
    IsZero ((constructibleIntegralPullback l E j).obj
      ((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).obj M))

/-- Closed support comparison and normalized restricted adjunction.
Source: latest blueprint, prop-sf-open-closed-triangle-all-stages.proof.md,
integral and rational support paragraphs; Stacks 03DI, 03DJ, 0941, 099N, 0GL1, 0A07
(blueprint: lem-sf-closed-support-normalization).

Proof:
1. Apply ordinary integral recollement realization to obtain closed. The actual
   quotient counit and ordinary pull comparison give closedReductionIso. Ringed
   open-closed localization makes completed module direct image exact, since the
   open complement is quasi-compact.
2. Scalar restriction and closed direct image commute sectionwise and with all
   quotient transitions. Conjugating the actual reduction square by its two
   adjunctions gives closedLimit. Applying ordinary image to the actual completion
   unit gives exactly closedAlpha. Direct-image/limit compatibility and Koszul
   reconstruction show this map invertible on complete constructible inputs;
   define di to be its inverse. The projection equations of the strict comparison
   give closedProjection, and the perfect projection formula gives the actual
   finite reduction isomorphisms closedReductionComparison.
3. Direct image preserves derived completeness. At finite level use constructible
   pro-etale origin, exact site comparison, and exact constructible closed etale
   image. Truncation triangles identify output cohomology with closed image of input
   cohomology, preserving the original interval.
4. Keep the ordinary pull comparison in closed. It is invertible on complete inputs
   by pull_complete; the consumer can therefore invert it to restrict the ordinary
   derived adjunction. No additional adjunction or pullback data is chosen here.
5. The strict projection maps and actual unit commute with shifted differentials
   and normalized Roos cone signs. Thus di preserves the specified shifts, and the
   right-derived/termwise comparison has its universal-unit shift. Exactness and
   constant-section scalar linearity descend and restrict to the full subcategories.
6. On an object over U, closed direct image evaluates on the empty fiber product
   with Z, hence vanishes. Exact derivation and the normalized pullback and di
   transport this zero composite to the stated actual constructible functors. -/
theorem closedSupportNormalization (D : FiniteFieldDatum.{u}) (primeUnit : IsUnit (l : D.k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] [i.IsOver (Spec (.of D.k))]
    (_hcomplement : Set.range j = (Set.range i)ᶜ) :
    Nonempty (ClosedSupport l E D primeUnit i j) := by
  sorry

end WeilConjectures.IntegralSupportNormalization
