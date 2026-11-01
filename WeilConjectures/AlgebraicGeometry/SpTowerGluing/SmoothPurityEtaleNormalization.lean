/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Normalization of the etale tower comparisons

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
Local pairs and Levels (blueprint: def-sp-tower-gluing-interfaces).

The graph coordinates and graph-normalization predicate are shared by the local
coordinate construction and global gluing. Refinement compatibility is a separate
tower equation for the supplied calculus, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

attribute [instance] GraphCoordinates.additive GraphCoordinates.inverseAdditive

end AlgebraicGeometry.ProEtale.SpTowerGluing

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

/-- The actual lifted quotient rings for the graph construction, with index n meaning n+1.
Source: Local pairs, coefficient convention (blueprint: det-sp-tower-gluing). -/
def graphRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))

/-- The adjacent quotient maps, lifted without changing coefficients.
Source: Local pairs, coefficient convention (blueprint: det-sp-tower-gluing). -/
def graphTransitions (n : ℕ) : graphRings l E (n + 1) ⟶ graphRings l E n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
      ULift.ringEquiv.toRingHom))

end AlgebraicGeometry.ProEtale.SpTowerGluing
