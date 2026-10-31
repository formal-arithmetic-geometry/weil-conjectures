/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedStageComparisonObligations
import WeilConjectures.AlgebraicGeometry.NormalizedStageComparisonPairing
import WeilConjectures.AlgebraicGeometry.NormalizedStageComparisonResidual
import WeilConjectures.AlgebraicGeometry.NormalizedStageComparisonSiteEquations

/-! # Coherence of the normalized finite-stage comparisons

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- Coherence of the fixed counit/evaluation comparisons and their four site squares.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraph 3;
the parent calculus plan, pairing, coefficient and site coherence clauses.
(blueprint: lem-sf-normalized-stage-comparison-coherence).

Proof: all tensorators are normalized by the same ordinary balanced tensor map and
all symmetries by the descended Koszul swap. On homogeneous tensors the two symmetry
paths have the same sign; on three coefficient factors both balanced paths multiply
the same scalars. Transpose the evaluation equation under tensor-Hom and use its
counit identity. Transpose the double-dual equation once more; substituting evaluation
twice gives the same pairing with the same Koszul interchange. Naturality follows
by transposing the corresponding naturality squares of counits and evaluation.
For identity arrows the multiplication unitor reduces each transpose to the original
counit or evaluation. For composites, the coefficient-projection cocycle and the
open-extension balancing formula give the compact-support cocycle. Mate pasting then
proves the closed and dualizing cocycles. Tensorator composition makes the two Hom
transposes equal, and composing with the dualizing cocycle proves the Verdier cocycle.
For proClosedMap insert the scalar/site mate definition and cancel the site unit and
counit by the adjunction triangles; this gives the closed site square. The same
calculation at the base regular unit gives the dualizing site square. Transposing
the Hom site square identifies both sides with scalar extension of site evaluation;
compose it with the dualizing square for Verdier. Constructible origin extends these
identities to all ctf pro-etale inputs. These calculations concern the fixed maps
and need no ambient pro-etale exceptional adjunction. The supplied pointwise and
site-isomorphism hypotheses justify each inverse comparison used in the transposes. In Lean,
the pairing, residual coefficient, and four site-square calculations are exposed as three
strictly smaller helper obligations and assembled field-by-field below. -/
theorem normalized_stage_comparison_coherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T X Z : Scheme.{u})
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k)))
    (μ : ∀ pro : Bool, ∀ {s t : Stage l E} (a : Arrow s t),
      Sites.TensorComparison pro a.ringMap X)
    (hμ : ∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
      Sites.NormalizedTensor pro a.ringMap X (μ pro a))
    (σ : ∀ (pro : Bool) (s : Stage l E),
      Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip)
    (hσ : ∀ (pro : Bool) (s : Stage l E),
      Sites.NormalizedSymmetry pro s.ring X (σ pro s))
    (hi : ∀ pro : Bool, Sites.StageComparisonIsomorphisms pro l E f i c (μ pro))
    (hsi : letI := c.hasCompactification
      Sites.StageComparisonSiteIsomorphisms l E f i c) :
    (∀ pro : Bool, Sites.StageComparisonCoherence pro l E f i c (μ pro) (σ pro)) ∧
      Sites.StageComparisonSiteEquations l E f i c (μ false) (μ true)  := by
  obtain hp := normalized_stage_comparison_pairing D l hl E T X Z f i c μ hμ σ hσ hi hsi
  obtain hr := normalized_stage_comparison_residual D l hl E T X Z f i c μ hμ σ hσ hi hsi
  obtain hs := normalized_stage_comparison_site_equations D l hl E T X Z f i c μ hμ σ hσ hi hsi
  refine ⟨?_, hs⟩
  intro pro
  have hp' := hp pro
  have hr' := hr pro
  refine {
    evaluation_eq := hp'.1
    bidual_eq := hp'.2
    closed_natural := hr'.closed_natural
    direct_unit := hr'.direct_unit
    closed_unit := hr'.closed_unit
    omega_unit := hr'.omega_unit
    hom_unit := hr'.hom_unit
    closed_comp := hr'.closed_comp
    omega_comp := hr'.omega_comp
    hom_comp := hr'.hom_comp }

end WeilConjectures.FiniteFreeCoefficients
