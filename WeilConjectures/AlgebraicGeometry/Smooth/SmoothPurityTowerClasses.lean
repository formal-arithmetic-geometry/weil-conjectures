/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal

/-! # Kummer and diagonal classes of coefficient towers
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale

open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (S : Scheme.{u})

/-- The canonical classes of coefficient towers: normalized Kummer Chern classes on `S`,
on the projective line and on the diagonal surface, with their finite-level normalizations,
the supported diagonal class, and the projective-line splitting `b_q` (an isomorphism)
whose trace kills the twisted unit and sends the hyperplane class to one. -/
structure TowerClasses (hS : IsUnit (l : Γ(S, ⊤))) where
  base : SpTowerShriek.Base l E
  chernS : Chern l E S
  chernP : Chern l E (ProjectiveLine S)
  chernW : Chern l E (diagonalSurface S)
  chernS_normalized : chernS.Normalized l E
  chernP_normalized : chernP.Normalized l E
  chernW_normalized : chernW.Normalized l E
  /-- Every finite evaluation is the finite Kummer boundary with the quotient
  source and the actual root-tensor target. -/
  chernS_levels : FiniteChernNormalization l E chernS
  chernP_levels : FiniteChernNormalization l E chernP
  chernW_levels : FiniteChernNormalization l E chernW
  twistS : Twisting l E chernS
  twistP : Twisting l E chernP
  diagonal : Diagonal l E base S chernW
  diagonal_levels : FiniteDiagonalNormalization l E diagonal
  projective : Projective l E base S chernS chernP twistS twistP
  /-- This is the actual biproduct map defined from the unit and c1(O(1)). -/
  [splitting : IsIso (projective.bq l E)]
  /-- The finite trace vanishes on the finite twisted-unit component. -/
  trace_unit :
    ∀ n : ℕ,
      (SpTowerShriek.Ev l E S n).map (projective.twistedUnit l E) ≫
        (SpTowerShriek.Ev l E S n).map (projective.trace l E) = 0
  /-- The finite trace sends the finite hyperplane class to one. Together with
  the finite projective-line decomposition this characterizes its usual trace. -/
  trace_chern :
    ∀ n : ℕ,
      (SpTowerShriek.Ev l E S n).map (projective.chernAdjoint l E) ≫
        (SpTowerShriek.Ev l E S n).map (projective.trace l E) =
          𝟙 ((SpTowerShriek.Ev l E S n).obj (SpTowerClasses.unit S (Arings l E S)))

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
