/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.IntegralSupportNormalizationData

/-! # Whole-system normalization of the open Hom transpose

Source: smooth-purity localization, the open adjunction and Hom vanishing paragraphs;
Stacks 03DI, 0941 and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary open Hom transpose agrees with the actual whole-system transpose.
This asserts only the pullback presentation and the Hom comparison. It does not
assert preservation of completeness or intervals, finite reduction, shifts, or exactness.

Source: latest blueprint, prop-sf-open-closed-triangle-all-stages.proof.md,
Hom vanishing paragraph and the open adjunction used for its triangle;
Stacks 03DI, 0941 and 0GL1.
(blueprint: lem-sf-open-support-adjunction-transpose).

Proof:
1. Apply the normalized immersion pullback comparison to j. Identify its ordinary
   coefficient presentation with ordinaryOpenPull by the coefficient isomorphism
   fixed by all quotient projections and constant sections. This gives p on the
   full constructible subcategory, without choosing a different strict pullback.
2. Apply integralOpenReductionComparison to the actual slice of j. Identify its
   completed and strict-system open functors with the specified ordinary functors
   by uniqueness of adjoints to their section-normalized restriction functors.
   Its system unit and counit equations identify the two Hom transposes. On a
   flat-term K-flat quotient representative both send a section x to x tensor 1;
   the quotient transitions preserve this equation. Exact localization therefore
   gives the equation for the whole derived system, before any finite evaluation.
3. The compact-support realization for (j,id) is normalized by these same quotient
   units. The section-normalized identity direct image removes its identity factor.
   Thus its whole-system comparison is compactOperationReduction followed by
   systemDirectId, and its ordinary comparison is exactly d below. Restrict the
   ordinary adjunction along the full inclusions. Apply its Hom transpose to f;
   the preceding system identity is precisely the displayed equality. The identity
   and empty opens, and zero input objects, use the same adjunction triangles.
   No faithfulness of evaluation is used. -/
theorem openAdjunctionTransposeNormalization (D : FiniteFieldDatum.{u})
    (primeUnit : IsUnit (l : D.k))
    {U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] :
    let d := (sfQcqsCompactSupportRealization l E D.k primeUnit
      (Compactification.ofIsOpenImmersion j)).symm ≪≫
        isoWhiskerLeft (sfIntegralConstructible l E U).ι (openIdentity l E j)
    ∃ p : constructibleIntegralPullback l E j ⋙ (sfIntegralConstructible l E U).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ ordinaryOpenPull l E j,
      let a := (ordinaryOpenAdjunction l E j).restrictFullyFaithful
        (sfIntegralConstructible l E U).fullyFaithfulι
        (sfIntegralConstructible l E X).fullyFaithfulι d.symm p.symm
      ∀ (N : sfIntegralConstructibleCategory l E U)
        (K : sfIntegralConstructibleCategory l E X)
        (f : (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
          (Compactification.ofIsOpenImmersion j) E).obj N ⟶ K),
        (FrobeniusExchange.reduction l E X).map f.hom =
          ((FrobeniusExchange.compactOperationReduction l E D.k primeUnit j
            (Compactification.ofIsOpenImmersion j)).app N ≫
            (systemDirectId l E X).hom.app
              ((FrobeniusExchange.systemDerivedOpen l E j).obj
                ((FrobeniusExchange.reduction l E U).obj N.obj))) ≫
          ((FrobeniusExchange.systemDerivedOpenAdjunction l E j).homEquiv _ _).symm
            ((FrobeniusExchange.reduction l E U).map ((a.homEquiv N K) f).hom ≫
              (integralComparisonPullbackCounit l E j
                ((FrobeniusExchange.models l E).system X)
                ((FrobeniusExchange.models l E).system U)
                ((FrobeniusExchange.models l E).roos U)
                ((FrobeniusExchange.models l E).pullback j)).app K.obj) := by sorry

end WeilConjectures.IntegralSupportNormalization
