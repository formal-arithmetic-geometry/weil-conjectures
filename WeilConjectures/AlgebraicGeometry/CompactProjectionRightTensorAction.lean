/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CondensedSupportProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ExactPullbackComparisonMonoidal

import WeilConjectures.CategoryTheory.UnitAdjunctTensorAction
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedPullbackCoherence

/-! # The native compactification projection as a right tensor action

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-identification/def-sf-cup.md, final associativity and unit sentence;
the native projection-input calculation expanded in the DAG
(blueprint: lem-sf-compact-projection-right-tensor-action).

The maps below use the ordinary unbounded internal-module categories, their relative
K-flat derived tensor, and the specified native adjunctions. No completion is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The inverse canonical open-support projection, with its target identified with native
left derived pullback by the landed canonical exact comparison `supportPullbackExactComparison`
(the `c_j` of lem-sf-exact-pullback-comparison-monoidal). The inverse is taken only after the
recorded support projection formula, applied to the actual closed complement, supplies
invertibility.
Source: def-sf-cup, projection construction
(blueprint: lem-sf-compact-projection-right-tensor-action). -/
def compactProjectionOpenInverse {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (supportModules Λ U)) (V : DerivedCategory (supportModules Λ X)) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.obj K ⊗ V ⟶
      (openImmersionLowerShriek Λ j).mapDerivedCategory.obj
        (K ⊗ (upperStar Λ j).leftDerivedFunctor.obj V) :=
  @inv _ _ _ _ (openSupportProjection Λ j K V)
      ((openClosedSupportProjectionFormula Λ j.closedComplement j
        j.range_closedComplement).2 K V) ≫
    (openImmersionLowerShriek Λ j).mapDerivedCategory.map
      (K ◁ (supportPullbackExactComparison Λ j).inv.app V)

/-- The inverse native compositor `Lj* Lp* ≅ Lf*`, including the specified factorization
identity of the compactification.
Source: def-sf-cup, native pullback compositor
(blueprint: lem-sf-compact-projection-right-tensor-action). -/
def compactProjectionPullbackCompositor {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (upperStar Λ c.g).leftDerivedFunctor ⋙ (upperStar Λ c.i).leftDerivedFunctor ≅
      (upperStar Λ f).leftDerivedFunctor :=
  ((upperStar Λ f).leftDerivedFunctorNatIso (upperStarCongr Λ c.comm) ≪≫
    leftDerivedUpperStarComp Λ c.i c.g).symm

/-- The precise compactification projection: the counit mate for `p`, the inverse
unit-induced open projection, then identity tensor the inverse native compositor.
Source: def-sf-cup, native projection-input construction
(blueprint: lem-sf-compact-projection-right-tensor-action). -/
def compactProjectionRightTensorMap {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (K : DerivedCategory (supportModules Λ X)) (N : DerivedCategory (supportModules Λ Y)) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⊗ N ⟶
      (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj
        (K ⊗ (moduleObjectDerivedPullback Λ f).obj N) :=
  letI : QuasiCompact c.obj.obj.i := c.obj.property
  moduleObjectProjectionMap Λ c.obj.obj.g
      ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K) N ≫
    (moduleObjectDerivedPushforward Λ c.obj.obj.g).map
      (compactProjectionOpenInverse Λ c.obj.obj.i K
        ((moduleObjectDerivedPullback Λ c.obj.obj.g).obj N)) ≫
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map
      (K ◁ (compactProjectionPullbackCompositor Λ c.obj.obj).hom.app N)

/-- The specified native projection is jointly natural and obeys the right tensor
associativity and unit equations for the native pullback's strong monoidal comparisons.
Source: def-sf-cup, final associativity and unit sentence; the expanded native calculation
(blueprint: lem-sf-compact-projection-right-tensor-action).

Proof plan, following the six DAG steps:
1. For `A = Lp*` and `R = Rp*`, the specified counit mate is the map of
   lem-sf-adjoint-right-projection-action, hence is natural, associative and unital.
   Its tensor comparison is exactly that of def-sfb-module-object-projection-map.
2. For `B = Lj*` and `J = j!`, transport the recorded open-support adjunction along
   the exact-open comparison. The monoidality of that comparison
   (lem-sf-exact-pullback-comparison-monoidal) identifies the transpose of the open
   projection with unit tensor identity followed by the forward tensorator of B.
   Apply lem-pur-unit-adjunct-tensor-action. The support projection formula makes
   this projection invertible; invert its action equation to obtain the equation
   for the gamma used here.
3. Transpose the open unit equation. The strong monoidal right-unit identity for B
   and right-unitor naturality identify its transpose with the unit followed by
   the source right unitor and unit comparison. Injectivity of the Hom bijection
   gives the open unit law. Naturality follows from the same transpose formula.
4. First use the composite pullback BA. Expand the two occurrences of
   H = R(gamma) followed after pi. Naturality of pi moves R(gamma) past the next
   pi. Apply the open and proper associativity laws and then gamma naturality.
   The resulting comparison is delta_B followed after B(delta_A).
5. For the unit, gamma naturality moves the unit comparison of A across gamma.
   Apply the open unit law, then the proper unit law. Naturality of H is inherited
   from pi and gamma.
6. The native inverse compositor d is monoidal by lem-fix-condensed-pullback-coherence:
   c followed after d equals (d tensor d) followed after delta_BA, and e followed
   after d at the unit equals the composite unit comparison. Substitute P = RJ(1 tensor d)H
   into steps 4 and 5 and use naturality to obtain the two equations below.
   Neither pi nor P is inverted. No boundedness, constructibility or finite Tor
   hypothesis occurs; the empty scheme and zero ring are allowed. -/
theorem compactProjectionRightTensorAction
    (k : Type u) [Field k] (_hchar : 0 < ringChar k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification f) :
    (∀ {K K' : DerivedCategory (supportModules Λ X)}
        {N N' : DerivedCategory (supportModules Λ Y)} (a : K ⟶ K') (b : N ⟶ N'),
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map a ⊗ₘ b) ≫
          compactProjectionRightTensorMap Λ c K' N' =
        compactProjectionRightTensorMap Λ c K N ≫
          (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map
            (a ⊗ₘ (moduleObjectDerivedPullback Λ f).map b)) ∧
    (∀ (K : DerivedCategory (supportModules Λ X))
        (N Q : DerivedCategory (supportModules Λ Y)),
      (compactProjectionRightTensorMap Λ c K N ▷ Q) ≫
          compactProjectionRightTensorMap Λ c (K ⊗ (moduleObjectDerivedPullback Λ f).obj N) Q ≫
          (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map
            (α_ K ((moduleObjectDerivedPullback Λ f).obj N)
              ((moduleObjectDerivedPullback Λ f).obj Q)).hom =
        (α_ ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K) N Q).hom ≫
          compactProjectionRightTensorMap Λ c K (N ⊗ Q) ≫
          (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map
            (K ◁ ((leftDerivedUpperStarTensorIso Λ f).hom.app N).app Q)) ∧
    (∀ K : DerivedCategory (supportModules Λ X),
      compactProjectionRightTensorMap Λ c K (𝟙_ (DerivedCategory (supportModules Λ Y))) ≫
          (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map
            (K ◁ (leftDerivedUpperStarUnitIso Λ f).hom) ≫
          (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map (ρ_ K).hom =
        (ρ_ ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
