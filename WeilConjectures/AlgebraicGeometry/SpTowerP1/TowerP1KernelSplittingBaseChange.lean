/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1KernelScalarData
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1ComparisonsWithLine
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerChernPullback
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # TowerP1KernelSplittingBaseChange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md.
(blueprint: lem-sp-tower-p1-kernel-splitting-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- Construct the unit/Chern splittings and their forward base-change square.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction of the triangle identities, base change of trace
(blueprint: lem-sp-tower-p1-kernel-splitting-base-change).

Proof: take the twisted projective-line splitting from TowerClasses. Its two
adjunct components give splittingQ_hom and its inverse projection is traceQ.
Use the coefficient and roots pullback maps normalized on sections to form the
comparisons for q and both projections. The relative hyperplane of projection a
is the pullback of O(1) along !a: on standard charts its basis and transition ratio
are unchanged. Chern pullback naturality identifies the second adjunct component.
The mate formula E = R'(w epsilon) eta', and naturality of eta', identify each
pulled-back adjunct with the adjunct at the base change. Thus the two components
of each splitting agree after exchange, yielding the displayed forward square.
The canonical direct-image composition comparison for p_a Delta = id is an
isomorphism; its mate word is exactly sourceUnitAt. This proves the source claim
for both projections, with no finiteness assumption on the base. -/
theorem towerP1KernelSplittingBaseChange (S : Scheme.{u})
    (hS : IsUnit (l : Γ(S, ⊤))) (p : Presentation l E S hS) :
    ∃ k : KernelSplittingData l E p,
      (∀ a : Bool, (SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.hom ≫
          k.exchange l E a = k.sumComparison l E ≫ (k.splittingProjection a).hom) ∧
      (∀ a : Bool, IsIso (p.sourceUnitAt l E a
        (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
