/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels

/-! # The normalized limit data used in diagonal pullback

Source: blueprint diagonal coefficient changes, paragraph (3).
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

/-- Named fields for the whole-system data of the diagonal limit. This structure
chooses no witnesses and imposes no new property on the completed class.

Source: the defining predicate `IsDiagonalLimit`, blueprint coefficient proof (3).
(blueprint: def-diagonal-class-limit-presentation). -/
structure ClassLimitPresentation (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))) where
  H : DiagonalSystems l (diagonalSurface Y)
  roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
    Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime)
  a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
    (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y))
  b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
    (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
    ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧
  c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2
  a_normalization : a.hom = diagonalDerivedSingleCounit l
    (diagonalScalarExtension l (diagonalSurface Y)) D (diagonalIntegralSource Y)
  boundary_normalization : c.hom =
    a.inv ≫ D.T.map (diagonalIntegralBoundary Y).hom ≫ b.hom
  finite_normalization : FiniteCartierNormalization l Y hY D.ordinary H roots c
  L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))
  s₀ : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
      (diagonalCompletedSource l Y) ≅
    limit (D.ordinary.E.obj (diagonalIntegralSource Y))
  t₀ : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H
  source_normalization : ∀ n : ℕ,
    diagonalCompletedGenerator l Y ≫ (diagonalForget l (diagonalSurface Y)).map
      (s₀.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
    (diagonalScalarAdjunction l (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
      (diagonalForget l (diagonalSurface Y)).map
        ((D.ordinary.π n).app (diagonalIntegralSource Y))
  target_normalization : HEq ((diagonalForget l (diagonalSurface Y)).map t₀.hom)
    (diagonalRootLimitComparison l (diagonalSurface Y) H roots).inv
  source_isIso : IsIso (diagonalSingleLimitComparison
    (diagonalCompletedRestriction l (diagonalSurface Y)) L
    (diagonalCompletedSource l Y) _ _ s₀ a)
  target_isIso : IsIso (diagonalShiftedSingleLimitComparison
    (diagonalCompletedRestriction l (diagonalSurface Y)) L
    (Scheme.purTwistZlModule (diagonalSurface Y) l) _ _ t₀ b)
  unique : ∃! δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y,
    (diagonalCompletedUnderlying l (diagonalSurface Y)).map δ ≫
        diagonalShiftedSingleLimitComparison
          (diagonalCompletedRestriction l (diagonalSurface Y)) L
          (Scheme.purTwistZlModule (diagonalSurface Y) l) _ _ t₀ b =
      diagonalSingleLimitComparison
          (diagonalCompletedRestriction l (diagonalSurface Y)) L
          (diagonalCompletedSource l Y) _ _ s₀ a ≫
        L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)

/-- The normalized source map of the entire derived limit.
Source: `IsDiagonalLimit` (blueprint: def-diagonal-class-limit-presentation). -/
def ClassLimitPresentation.sourceMap {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    {hY : IsUnit (l : Γ(Y, ⊤))}
    {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
    (d : ClassLimitPresentation l Y hY D) :=
  diagonalSingleLimitComparison (diagonalCompletedRestriction l (diagonalSurface Y))
    d.L (diagonalCompletedSource l Y) _ _ d.s₀ d.a

/-- The normalized target map of the entire derived limit.
Source: `IsDiagonalLimit` (blueprint: def-diagonal-class-limit-presentation). -/
def ClassLimitPresentation.targetMap {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    {hY : IsUnit (l : Γ(Y, ⊤))}
    {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
    (d : ClassLimitPresentation l Y hY D) :=
  diagonalShiftedSingleLimitComparison (diagonalCompletedRestriction l (diagonalSurface Y))
    d.L (Scheme.purTwistZlModule (diagonalSurface Y) l) _ _ d.t₀ d.b

/-- A normalized completed class supplies the named whole-system presentation.

Source: the definition of `IsDiagonalLimit`.
(blueprint: def-diagonal-class-limit-presentation).

Proof: unpack its witnesses, retain the ordinary endpoint normalizations, and
retain the isomorphism and uniqueness parts of its compatibility assertion.
The defining whole-system arrow equation is unchanged. -/
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

/-- Uniqueness in the full limit equation identifies a proposed completed class.

Source: the uniqueness clause of `IsDiagonalLimit`.
(blueprint: def-diagonal-class-limit-presentation).

Proof: the asserted equality after restriction gives the defining whole-system
equation for the proposed arrow. Apply uniqueness to the two solutions. -/
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
