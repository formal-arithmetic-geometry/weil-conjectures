/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence
import Sheaf.Paper.QcqsCompactSupportReductionRigidity

/-! # The normalized qcqs compact-support morphism

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tag 0F7J
(blueprint: lem-qcqs-compact-support-normalized-lift).

The object values and the integral and rational actions are the published ones.
The comparison below retains their chosen Roos projections, on every constructible
integral input, without requiring the schemes themselves to be separated over the field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
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
(blueprint: lem-qcqs-compact-support-normalized-lift). -/
def SfQcqsCompactSupportMorphismSpec
    (τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E Y n).map (τ.app K) ≫
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom =
      (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K.obj) ≫
        (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K.obj ≫
        (finiteImageIso l E n c).hom.app
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K.obj) ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((finiteReductionIso l E X n).hom.app K.obj)

/-- The finite proper/open mates lift to one natural morphism into the recorded
integral action, uniquely with their prescribed projection normalization. Invertibility
is a separate assertion: this theorem constructs and identifies a morphism only.

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tags 0941 and 0F7J
(blueprint: lem-qcqs-compact-support-normalized-lift).

Proof: use the coherent compact-support reduction tower, including its actual quotient
transitions, and the total right-derived limit and projection-normalized comparison
recorded in `exists_compactSupportRepresentativeComparison`. On strict K-flat input
complexes the open scalar-adjunction mate is the extension-summand tensor map. Apply
proper direct image to that whole diagram, and its right-adjunction comparison with
total inverse limit. The source augmentation is the canonical completion unit.
The resulting natural morphism into the total limit transports through the recorded
gamma to the specified integral action. Transpose each projection through the fixed
scalar adjunction: the unit/counit identities give exactly the displayed equation,
including `finiteReductionIso` and `finiteImageIso` as its endpoint coordinates.
The construction commutes with roofs since all transformations are derived on whole
strict complexes. For uniqueness use those normalized universal comparisons on strict
resolutions and the total-limit adjunction, before evaluation; the prescribed projection
mates are the same universal counit, and its Hom transpose is unique. Transport back
through gamma gives equality of the natural morphisms. This last step is a rigidity
statement for these functors and this normalization, not a claim that unrelated finite
evaluations are faithful on a derived category. Zero input and the empty scheme cause
no change to the universal comparison or its naturality. -/
theorem sfQcqsCompactSupport_normalizedLift_existsUnique :
    ∃! τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι,
      SfQcqsCompactSupportMorphismSpec l E K₀ hl c τ := by
  obtain ⟨σ, hσ⟩ := sfQcqsCompactSupport_normalizedIso_exists l E K₀ hl c
  let τ := σ.hom
  have hτ : SfQcqsCompactSupportMorphismSpec l E K₀ hl c τ := hσ
  refine ⟨τ, hτ, fun τ' hτ' ↦ ?_⟩
  apply sfQcqsCompactSupport_reduction_ext l E K₀ hl c τ' τ
  intro K n
  apply (cancel_mono (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom).mp
  exact (hτ' K n).trans (hτ K n).symm

end WeilConjectures
