/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.Paper.RationalP1SecondProjectionInterchangeCore
public import Sheaf.Paper.RationalP1SecondPullComparison

/-! Explicit fixed projection-tail cancellation after removing the dead let bindings. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- Fixed tail cancellation with the unused local bindings eliminated.
Source: the second identity of the rational projective-line triangle calculation.
The reduction first unfolds the three fixed maps and then performs the
associator, projection-mate, tensor-shift, and line-comparison cancellations.
(blueprint: lem-sfb-rational-p1-second-projection-interchange-tail-expanded). -/
theorem second_projection_tail_cancellation_expanded
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    let Λ := (coefficient l c).X
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let H := twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))
    let Q := (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    let T := (((DerivedCategory.singleFunctor
      (Modules Λ (diagonalSurface Y)) 0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    secondTraceStrengthTail Λ Y (line l c (ProjectiveLine Y)) K Q ≫
        H.map (secondExtractProjection l c k p hpl Y K) ≫
        twistProjectionMap Λ (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj (H.obj (F.obj K))) =
      (projectionMap Λ (secondProjection Y))
        (H.obj (F.obj K)) T ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (tensorHom (secondPullComparison l c k p hpl Y K).inv (𝟙 T) ≫
            (tensorShiftIso Λ (diagonalSurface Y) (line l c (diagonalSurface Y))
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
            (H.obj (F.obj K)))).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
 
