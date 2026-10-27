/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.CompactificationCompletedRealizationData

/-! # Finite counit projections in normalized completed-operation coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactificationCompletedRealization
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- Choose normalized tensor and pullback models simultaneously with their finite
coefficient coordinates; the ordinary counit projection commutes with reduction.
Source: blueprint sk-prop-sf-pf-reduction, final paragraph;
Stacks 07A6, 0B56, 099N
(blueprint: lem-fix-compactification-finite-projection-models).

Proof: construct ordinary tensor on flat-term K-flat representatives and completed
pullback from the actual scalar pullback followed by quotient completion. The
representative tensor and pullback comparisons, normalized on pure tensors and on
their completion units, provide aX, aZ, aY and b. Use the analogous ordinary tensor
models over each positive finite quotient. The constant-ring pullback compositor
supplies the finite composition field. Restriction of coefficients identifies
ordinary geometric pullback and direct image as an adjoint pair and preserves its
unit and counit. Tensor scalar extension is the pure-tensor comparison; the open
extension tensor comparison has identity restriction to the open. Consequently the
proper counit projection followed by the open tensor projection commutes with
scalar extension in these coordinates. Naturality of the compact-support scalar
comparison moves the subsequent argument augmentation to the finite target.
Cancel the inverse scalar tensor/pullback comparison at that target. This gives
exactly FiniteProjectionEquation, including its final reduced argument unit.
No completion unit is inverted in this finite equation and no Tor bound is used. -/
theorem finiteProjectionModels [QuasiCompact c.i] :
    ∃ (aX : OpenFactorCoherence.Tensor l E X)
      (aZ : OpenFactorCoherence.Tensor l E c.Z) (aY : OpenFactorCoherence.Tensor l E Y)
      (b : OpenFactorCoherence.Pull l E f) (d : ∀ n : ℕ, FiniteCoordinates l E c n),
      ∀ (K : sfIntegralConstructibleCategory l E X)
        (L : sfIntegralConstructibleCategory l E Y) (n : ℕ),
        FiniteProjectionEquation l E c n (d n) aX aZ aY b K.obj L.obj := by
  sorry

end WeilConjectures.CompactificationCompletedRealization
