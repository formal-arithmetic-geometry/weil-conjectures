/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceStrictTransformPresentation

/-! # Module strict transforms on algebraic spaces

Source: Stacks Project, Divisors on Spaces, Tag 0862(1), definition-strict-transform
(blueprint: def-sfb-space-module-strict-transform-presentation).

The quotient and its entire kernel are retained. The covering sieve allows torsion
exponents to vary locally, and the centre ideal remains part of the parameters.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The quotient of the tensor pullback by exceptional power torsion, specified together
with its quotient map. An epimorphism and its complete kernel determine this quotient
up to a unique isomorphism preserving that map. The restriction to all further tests
expresses annihilation by the ideal sheaf, without requiring global generators.
On a chart with exceptional equation t this says locally t^n m = 0.
Source: Stacks Project, Divisors on Spaces, Tag 0862(1)
(blueprint: def-sfb-space-module-strict-transform-presentation). -/
structure ModuleStrictTransformPresentation {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) (K : QuasiCoherentIdeal T) (B : BlowupPresentation K)
    (P : StrictTransformPresentation f K B) (M : X.Modules) where
  /-- The quotient module on the ambient fibre product. -/
  module : P.ambient.Modules
  /-- The quotient of the canonical tensor pullback. -/
  quotient : (moduleTensorPullback P.toSource).obj M ⟶ module
  /-- Surjectivity as a morphism of module sheaves. -/
  epi : Epi quotient
  /-- Exactly the locally exceptional-power-torsion sections form the kernel. -/
  kernel : ∀ (V : P.ambient.EtaleSite)
    (s : ((moduleTensorPullback P.toSource).obj M).val.obj (op V)),
    quotient.val.app (op V) s = 0 ↔
      ∃ R : Sieve V, R ∈ P.ambient.etaleTopology V ∧
        ∀ (W : P.ambient.EtaleSite) (a : W ⟶ V), R a →
          ∃ n : ℕ, ∀ (Z : P.ambient.EtaleSite) (b : Z ⟶ W),
            ∀ r ∈ idealSectionImage (idealTensorMap (P.toBlowup ≫ B.projection) K) Z ^ n,
              r • ((moduleTensorPullback P.toSource).obj M).val.map (b ≫ a).op s = 0

end AlgebraicGeometry.AlgebraicSpace
