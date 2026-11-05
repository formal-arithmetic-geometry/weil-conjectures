/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernBaseChangeUnit
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernBaseChangeChern

/-! # Exchange on the two actual Chern generators

Source: diagonal-tower unit/Chern splitting and the second rational P1 triangle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line diagram trace singleUnitIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The self-square exchange preserves the twisted unit and positive Chern
adjuncts. This is an equation on each specified generator, before any trace
or inverse splitting is applied.

Source: latest blueprint, sk-prop-diagonal-tower-coefficients.proof.md (3a)--(3c),
and sk-prop-p1-adjunction-rational-triangle.proof.md, second identity
(blueprint: lem-sfb-rational-p1-scalar-chern-base-change).

Proof: Expand the exchange as the adjunction mate. The adjunction triangle and
the pullback-composition comparison identify the image of the twisted unit
with the p2 twisted unit after the q line comparison. For the second component,
pull the positive Cartier class of the standard section along q. In the product
model this is the section of the second projection: r.q_model is the identity
model, and r.p2_model is the factor-swapped product model. On the affine chart
the section equation is t, which remains a nonzerodivisor over every base. The
units pullback and generator t^-1 preserve its positive quotient generator +1.
Consequently the complete Kummer-system diagram commutes, including all root
transitions. Apply its actual derived limit and normalized unit/line comparisons;
ha and hb identify the resulting completed Chern adjuncts. The full universal
units in Reference carry its mate to the condensed exchange. Apply the actual
scalar-extension functors and their normalized mates; mate pasting commutes
with this geometric square. Family's root and unit endpoint normalizations
identify the endpoint maps with firstLineComparisonForTrace, scalarQLineIso and
scalarUnitPullIso. Apply the bottom finite-field leg for the closure coefficient,
whose comparisons are already invertible in Family.toClosure. This proves the
two displayed generator equations, without using a trace, a diagonal class,
an integration equation or invertibility of the geometric exchange. -/
theorem scalar_chern_base_change
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
    let L := line l c
    let T := fun X : Scheme.{u} ↦
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (L X)) ⟦(2 : ℤ)⟧
    let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
      (scalarQLineIso l c k p hpl Y)
    let u₂ := scalarTwistedUnit Λ (secondProjection Y)
      (T (ProjectiveLine Y)) (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
    let cq := scalarQChern l c Y r a
    let c₂ := scalarP2Chern l c Y r b
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    F.map uq ≫ secondTraceExchange l c k p hpl Y =
        (scalarQLineIso l c k p hpl Y).hom ≫ u₂ ∧
      F.map cq ≫ secondTraceExchange l c k p hpl Y =
        (scalarUnitPullIso Λ Y).hom ≫ c₂ := by
  dsimp only
  exact ⟨scalar_chern_base_change_unit l c k p hpl Y δ family r a ha b hb,
    scalar_chern_base_change_chern l c k p hpl Y δ family r a ha b hb⟩

end AlgebraicGeometry.ProEtale.RationalP1
