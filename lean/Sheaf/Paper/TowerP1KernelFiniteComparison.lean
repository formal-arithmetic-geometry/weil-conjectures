/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.Paper.TowerP1KernelScalarData
import Sheaf.Paper.TowerP1EtaleOriginComparisons
import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalCartier

/-! # TowerP1KernelFiniteComparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md.
(blueprint: lem-sp-tower-p1-kernel-finite-comparison).
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

/-- Identify the normalized diagonal scalar at each finite level.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Levelwise check, finite diagonal integrals
(blueprint: lem-sp-tower-p1-kernel-finite-comparison).

Proof: the diagonal is Cartier on the two standard projective charts. At each
positive level n+1 use the canonical constant, root, tensor and site-mate
coordinates supplied by the etale-origin comparisons. The supported diagonal
normalization identifies the evaluated delta with the finite Kummer boundary
with positive divisor sign. Mate pasting for p_a Delta = id identifies alpha
with the ordinary composition source. The unit/Chern characterization of the
splitting identifies its inverse second projection with the finite trace along
the standard chart for p_a. These give alpha, pushed_delta and trace equations;
compose those commuting squares to get the composite equation. The coefficient
ring is finite by Base.finite; N = l^(n+1) is positive, annihilates it, and is
invertible on S. The arbitrary-base finite diagonal integrals give finite_identity
for both projections. Their canonical twist transport and normalized splitting
are the chosen finite coordinates. No equality detection on arbitrary derived
morphisms is used: this lemma asserts only the finite commuting squares. -/
theorem towerP1KernelFiniteComparison (S : Scheme.{u})
    (hS : IsUnit (l : Γ(S, ⊤))) (p : Presentation l E S hS)
    (k : KernelSplittingData l E p) :
    ∃ hD : (diagonalImmersion S).ker.IsInvertible,
      ∀ n : ℕ, k.finiteNormalization l E hD n := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
