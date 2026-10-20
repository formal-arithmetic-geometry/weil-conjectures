/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

/-! # Compact-support realization without separated structure morphisms

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tag 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

The object values and the integral and rational actions are the published ones.
The comparison below retains their chosen Roos projections, on every constructible
integral input, without requiring the schemes themselves to be separated over the field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- Projection normalization for the ambient realization of the recorded integral functor.
The finite comparison is the actual scalar-adjunction mate of open extension followed
by proper image; its source projection is the chosen Roos projection, not a freely
chosen reduction isomorphism. Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-weil-integral-rational-qbar-compact-support). -/
def SfQcqsCompactSupportRealizationSpec
    (τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E Y n).map (τ.hom.app K) ≫
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom =
      (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K.obj) ≫
        (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K.obj ≫
        (finiteImageIso l E n c).hom.app
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K.obj) ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((finiteReductionIso l E X n).hom.app K.obj)

/-- The projection-normalized realization on the whole integral constructible category.
Source: Bhatt--Scholze, Definition 6.7.6, Lemmas 6.7.7 and 6.1.13
(blueprint: def-weil-integral-rational-qbar-compact-support).

Proof: use the coherent reduction tower of
lem-weil-compact-support-reduction-tower-functor and its actual total right-derived
limit. The integral residue-Tor theorem supplies a common finite Tor interval for all
reductions of each constructible input. Completed open extension commutes with that
normalized tower, using its completion unit. Proper image commutes with total limit
by the right-adjunction comparison. Their composite identifies the actual proper/open
functor, on objects and roofs, with the recorded integral action. The normalized
universal comparisons carry its finite scalar mates to the chosen Roos projections,
which gives the displayed equation and uniqueness. All schemes occurring are finite
type over a field, hence Noetherian and qcqs; none of these arguments uses separatedness
of a structure morphism. The only separated morphism is f, as in the definition. -/
theorem sfQcqsCompactSupportRealization_existsUnique :
    ∃! τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι,
      SfQcqsCompactSupportRealizationSpec l E K₀ hl c τ := by
  sorry

/-- The canonical realization fixed by the preceding projection normalization.
Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-weil-integral-rational-qbar-compact-support). -/
def sfQcqsCompactSupportRealization :
    (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι :=
  (sfQcqsCompactSupportRealization_existsUnique l E K₀ hl c).exists.choose

end WeilConjectures
