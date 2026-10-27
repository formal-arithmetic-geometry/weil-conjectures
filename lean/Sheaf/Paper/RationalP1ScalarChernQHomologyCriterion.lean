/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RationalP1ScalarChernMaps

/-! # Homological criterion for the scalar q splitting

Source: diagonal-tower unit/Chern splitting and the first rational P1 triangle.
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

attribute [local irreducible] coefficient line diagram trace singleUnitIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The componentwise homological data needed by the abstract q biproduct criterion.

Source: the positive twist and shift of the diagonal tower splitting, followed by
restriction, completion, realization and scalar extension in the first rational
P1 triangle (blueprint: lem-sfb-rational-p1-scalar-q-homology-criterion).

Proof: evaluate the normalized completed splitting on strict constant systems,
transport its two components through the prescribed realization and scalar mates,
and use projective-line cohomological concentration in degrees `0` and `-2`.
The normalized Chern equation identifies the degree-zero component with the actual
scalarQChern arrow, while the unit component identifies the degree-minus-two map
with scalarTwistedUnit. The same concentration gives vanishing of the pushforward
in all other degrees, and the endpoint comparisons preserve invertibility. -/
theorem scalar_q_chern_homology_criterion
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    let Λ := (coefficient l c).X
    let T := fun X : Scheme.{u} ↦
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (line l c X)) ⟦(2 : ℤ)⟧
    let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
      (scalarQLineIso l c k p hpl Y)
    let cq := scalarQChern l c Y r a
    let U := unit Λ Y
    let V := T Y
    let K := (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      (T (ProjectiveLine Y))
    (∀ n : ℤ, n ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (Modules Λ Y) n).obj U)) ∧
      (∀ n : ℤ, n ≠ -2 → IsZero
        ((DerivedCategory.homologyFunctor (Modules Λ Y) n).obj V)) ∧
      (∀ n : ℤ, n ≠ 0 → n ≠ -2 → IsZero
        ((DerivedCategory.homologyFunctor (Modules Λ Y) n).obj K)) ∧
      IsIso ((DerivedCategory.homologyFunctor (Modules Λ Y) 0).map cq) ∧
      IsIso ((DerivedCategory.homologyFunctor (Modules Λ Y) (-2)).map uq) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
