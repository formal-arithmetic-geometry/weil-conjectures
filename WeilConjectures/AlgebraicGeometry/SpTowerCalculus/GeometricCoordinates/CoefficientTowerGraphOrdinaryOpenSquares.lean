/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerRealizedProperOpenCoordinates
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore

/-! # Ordinary squares for the fixed graph presentations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Equality of the two ordinary open models.
Source: Local pairs, fixed section model
(blueprint: lem-sp-graph-ordinary-open-squares). -/
theorem graph_extension_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    SemilinearProperOpen.extension (graphRings l E) (graphTransitions l E) j =
      VaryingRing.extension (graphRings l E) (graphTransitions l E) j := by
  exact SemilinearProperOpen.extension_eq _ _ j

/-- Equality of the ordinary inverse-image models.
Source: Local pairs, fixed section model
(blueprint: lem-sp-graph-ordinary-open-squares). -/
theorem graph_pull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.pull (graphRings l E) (graphTransitions l E) f =
      VaryingRing.pull (graphRings l E) (graphTransitions l E) f := by
  exact SemilinearProperOpen.pull_eq _ _ f

/-- The forward ordinary inverse-image square.
Source: Local pairs, adjunction-normalized graph coordinates
(blueprint: lem-sp-graph-ordinary-open-squares). -/
def graphPullSquare (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (o.geometry f).pull ⋙ (g.presentation X).functor ≅
      (g.presentation Y).functor ⋙
        VaryingRing.pull (graphRings l E) (graphTransitions l E) f :=
  graphForward l E b o g _ _ (graphPullCoordinates l E b o g f) ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (graph_pull_eq l E f))

/-- The forward ordinary extension square.
Source: Local pairs, adjunction-normalized graph coordinates
(blueprint: lem-sp-graph-ordinary-open-squares). -/
def graphOpenSquare (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (o.openOp j).extension ⋙ (g.presentation X).functor ≅
      (g.presentation U).functor ⋙
        VaryingRing.extension (graphRings l E) (graphTransitions l E) j :=
  graphForward l E b o g _ _ (graphOpenCoordinates l E b o g j) ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (graph_extension_eq l E j))

/-- The ordinary compositor defining sequenceOpenComposition.
Source: Local pairs, composition of the specified open adjunctions
(blueprint: lem-sp-graph-ordinary-open-squares). -/
def graphOrdinaryOpenComp (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {U X Z : Scheme.{u}}
    (j : U ⟶ X) (i : X ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion i] :
    (o.openOp j).extension ⋙ (o.openOp i).extension ≅ (o.openOp (j ≫ i)).extension :=
  (((o.openOp j).ordinaryAdjunction.comp (o.openOp i).ordinaryAdjunction).ofNatIsoRight
    (o.ordinaryComp j i)).leftAdjointUniq (o.openOp (j ≫ i)).ordinaryAdjunction

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
