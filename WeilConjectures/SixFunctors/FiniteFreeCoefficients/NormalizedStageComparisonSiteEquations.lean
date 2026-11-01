/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations

/-! # Site equations for normalized stage comparisons

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

/-- The fixed coefficient/site bridges satisfy the four site squares.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--3;
(blueprint: lem-sf-normalized-stage-comparison-site-equations).

Proof: insert the prescribed scalar/site mate definitions for the closed and dualizing
maps and cancel the site units and counits by the adjunction triangles. Transpose the
Hom square to scalar extension of site evaluation and compose it with the dualizing
square for Verdier. Constructible origin and naturality extend the equalities from the
finite etale presentations to all ctf pro-etale inputs. -/
theorem normalized_stage_comparison_site_equations
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
    Sites.StageComparisonSiteEquations l E f i c (μ false) (μ true) := by
  sorry

end WeilConjectures.FiniteFreeCoefficients
