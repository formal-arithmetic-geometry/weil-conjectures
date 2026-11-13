/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.ClassLimitPresentation.DiagonalClassLimitPresentation

/-! # Maps and existence for the normalized diagonal limit presentation

The source and target maps of `ClassLimitPresentation` and its existence and uniqueness
statements, split off from `DiagonalClassLimitPresentation` to keep the time needed to compile
each module below the build limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison

/-- The normalized source map of the entire derived limit. -/
def ClassLimitPresentation.sourceMap {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    {hY : IsUnit (l : Γ(Y, ⊤))}
    {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
    (d : ClassLimitPresentation l Y hY D) :=
  diagonalSingleLimitComparison (diagonalCompletedRestriction l (diagonalSurface Y))
    d.L (diagonalCompletedSource l Y) _ _ d.s₀ d.a

/-- The normalized target map of the entire derived limit. -/
def ClassLimitPresentation.targetMap {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    {hY : IsUnit (l : Γ(Y, ⊤))}
    {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
    (d : ClassLimitPresentation l Y hY D) :=
  diagonalShiftedSingleLimitComparison (diagonalCompletedRestriction l (diagonalSurface Y))
    d.L (Scheme.purTwistZlModule (diagonalSurface Y) l) _ _ d.t₀ d.b

/-- A normalized completed class supplies the named whole-system presentation. -/
theorem classLimitPresentation_exists (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ) :
    ∃ d : ClassLimitPresentation l Y hY D,
      (diagonalCompletedUnderlying l (diagonalSurface Y)).map δ ≫
          diagonalShiftedSingleLimitComparison
            (diagonalCompletedRestriction l (diagonalSurface Y)) d.L
            (Scheme.purTwistZlModule (diagonalSurface Y) l) _ _ d.t₀ d.b =
        diagonalSingleLimitComparison
            (diagonalCompletedRestriction l (diagonalSurface Y)) d.L
            (diagonalCompletedSource l Y) _ _ d.s₀ d.a ≫
          d.L.R.map (D.T.map (diagonalIntegralBoundary Y).hom) := by
  rcases hδ with ⟨H, roots, a, b, c, ha, hc, hfinite, L, M, s₀, t₀,
    ⟨hs, ht, hcompat⟩, hwhole⟩
  refine ⟨⟨H, roots, a, b, c, ha, hc, hfinite, L, s₀, t₀, hs, ht,
    hcompat.1, hcompat.2.1, hcompat.2.2.2.2.1⟩, hwhole⟩

/-- Uniqueness in the full limit equation identifies a proposed completed class. -/
theorem ClassLimitPresentation.eq_of_map_eq (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (d : ClassLimitPresentation l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : (diagonalCompletedUnderlying l (diagonalSurface Y)).map δ ≫
          diagonalShiftedSingleLimitComparison
            (diagonalCompletedRestriction l (diagonalSurface Y)) d.L
            (Scheme.purTwistZlModule (diagonalSurface Y) l) _ _ d.t₀ d.b =
        diagonalSingleLimitComparison
            (diagonalCompletedRestriction l (diagonalSurface Y)) d.L
            (diagonalCompletedSource l Y) _ _ d.s₀ d.a ≫
          d.L.R.map (D.T.map (diagonalIntegralBoundary Y).hom))
    (δ' : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (h : (diagonalCompletedUnderlying l (diagonalSurface Y)).map δ' =
      (diagonalCompletedUnderlying l (diagonalSurface Y)).map δ) : δ' = δ := by
  exact d.unique.unique (by rw [h]; exact hδ) hδ

end AlgebraicGeometry.ProEtale.DiagonalTrace
