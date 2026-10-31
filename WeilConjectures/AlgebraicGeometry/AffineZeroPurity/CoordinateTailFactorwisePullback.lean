/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorCup

/-! # Factorwise pullback data for the successor tail product -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- The chosen square for one old divisor.
Source: coordinate zero-locus pullback in the ordered exterior product.
(blueprint: lem-pur-coordinate-tail-factorwise-pullback). -/
def tailDivisorSquare (B : Scheme.{u}) (r : ℕ) (i : Fin r) :
    ChosenCartesianSquare (successorDivisorProjection B r i)
      (inclusion B (r + 1) i.succ) (inclusion B r i) (lastProjection B r) where
  toCommSq := (successorDivisor_isPullback B r i).toCommSq
  isoPullback := (successorDivisor_isPullback B r i).isoPullback
  hom_fst := (successorDivisor_isPullback B r i).isoPullback_hom_fst
  hom_snd := (successorDivisor_isPullback B r i).isoPullback_hom_snd

/-- The exact single comparison of the normalized closed coefficient exchange.
Source: closed-constant normalization in the ordered exterior product.
(blueprint: lem-pur-coordinate-tail-factorwise-pullback). -/
def tailDivisorSourcePullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (r : ℕ) (i : Fin r) :=
  pullbackSingle (setting P n).Coefficient (lastProjection B r) _ _
    ((setting P n).functorialCupExchange true (inclusion B r i)
      (inclusion B (r + 1) i.succ) (lastProjection B r)
      (successorDivisorProjection B r i) (tailDivisorSquare B r i))

/-- The realized pullback equation for one old coordinate factor.
Source: the Cartier-map pullback sentence of the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-tail-factorwise-pullback).
Proof: the coordinate indexed by `i.succ` is the pullback of coordinate `i`, so
`successorDivisor_isPullback` gives the Cartier square. Project the ordinary
Cartier family's normalization and apply supported_kummer_boundary_pullback at
exponent l^(n+2). Apply Ext.hom and exact etale-to-pro-etale comparison. Naturality
of the single and shift comparisons moves inverse image through realizeBoundary.
The closed-source comparison agrees with functorialCupExchange: precompose both
with constant restriction, use the site-comparison square, and cancel the epic
restriction. The Tate-line comparison agrees with shiftedLinePullback since
both carry each pulled-back root to the same root; the root-normalized transport
uniqueness identifies them. Cancel the invertible source comparison to obtain
the displayed equation. No flatness or finite-type assumption is used. -/
theorem coordinate_tail_factorwise_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) (i : Fin r) :
    (tailDivisorSourcePullback P n B r i).inv ≫
        (inverseImage (setting P n).Coefficient (lastProjection B r)).map
          (boundary P n B aB r i) ≫
        (shiftedLinePullback (setting P n) (lastProjection B r) (towerBase aB r)).hom =
      boundary P n B aB (r + 1) i.succ := by
  sorry

end AlgebraicGeometry.ProEtale.AffineZeroPurity
