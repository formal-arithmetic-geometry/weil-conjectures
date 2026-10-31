/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernLocalFactorization

/-! # Pullback of the local scalar Chern classes

Source: geometric tower classes (2), and diagonal coefficient changes (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

/-- Pulling the local section class along p1 gives the section class of p2.
This is an equation of local classes on the product; it has no direct images,
exchange mate, completed Chern adjuncts, traces, or splitting maps.

Source: geometric tower classes (2), Chern pullback; diagonal coefficient changes
(1), whole-system unit and root comparisons; rational P1 second triangle.
(blueprint: lem-sfb-rational-p1-scalar-local-chern-pullback).

Proof: q_model identifies the q model bundle with O(1). The factor-swapped product
model p2_model identifies its bundle with p1*O(1), by the base-change identification
of the tautological invertible module. Apply tower_firstChern_pullback to that
bundle, using the coefficient-one and root-normalized comparisons. Its proof uses
the pullback square for the integral line-bundle extension and the positive
Kummer boundary, so it is an equality of entire systems. Apply constant-scalar
restriction and the inverse-image/derived-limit comparison. The unit and root
limit comparisons make that comparison invertible on these endpoints; naturality
and the two CompletedLocalChernNormalized equations give the local completed
square. Transport it through eP and eW. Their underlying-sheaf normalizations
identify the ordinary inverse-image comparisons; their unit projections and root
projections identify the two endpoints. Apply scalar extension Z_l -> O_E -> E
to this local square. Scalar/inverse-image composition is fixed on the units by
one and on the Tate lines by the balanced tensor root map, so the endpoint
normalizations identify the result with scalarQLocalChern and scalarP2LocalChern.
The coefficient-unit composition law around the self-square identifies the source
comparison with the displayed ambientPullbackComparison followed by the q unit
comparison; its other side is the p2 pullback of the q unit comparison followed by
the p2 unit comparison. The target comparison is firstLineComparisonForTrace by
its root normalization, with the canonical degree-two shift. This gives the
displayed equation. This uses no faithfulness of finite-level evaluation, and
works on the empty scheme and for arbitrary base changes. -/
theorem scalar_local_chern_pullback
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧)
    (hz : CompletedLocalChernNormalized l r.tq.toPresentation z)
    (w : DiagonalTrace.completedUnit l (diagonalSurface Y) ⟶
      (DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧)
    (hw : CompletedLocalChernNormalized l r.t₂.toPresentation w) :
    let Λ := (coefficient l (some E)).X
    (ambientPullbackComparison Λ (square Y)).hom.app (unit Λ Y) ≫
        (moduleObjectDerivedPullback Λ (firstProjection Y)).map
          ((scalarUnitPullIso Λ Y).hom ≫ scalarQLocalChern l E Y r z) ≫
        (firstLineComparisonForTrace l (some E) k p hpl Y).hom =
      (moduleObjectDerivedPullback Λ (secondProjection Y)).map
          (scalarUnitPullIso Λ Y).hom ≫
        (scalarP2UnitIso Λ Y).hom ≫ scalarP2LocalChern l E Y r w := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
