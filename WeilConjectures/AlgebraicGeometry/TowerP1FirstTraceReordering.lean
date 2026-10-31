/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerP1TriangleWords

/-! # Internal reordering for projective-line tower triangles

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction of the triangle identities (blueprint: lem-sp-tower-p1-triangle-factorization).
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

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- The diagonal-free first trace rearrangement. Its source is the direct image
of p1*M tensor T_W, not FM. Thus it can be used before any supported class is inserted.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction, first triangle; the explicit argument is steps 2--4 of the parent node
(blueprint: lem-sp-tower-p1-first-trace-reordering).

Proof: write L=q*, R=Rq*, a=p1*, b=p2*, U=Rp1*, V=Rp2*, and T=A_P(1)[2].
Use the recorded pullback square to identify aL with bL and its adjunction conjugate
pushSwap to identify RV with RU. Form J1 and J2 from RM tensor RT to RU(aM tensor T_W).
J1 is the q projection, tensor with the swapped exchange at T, then the p1 projection.
J2 is the q projection at (RM,T), tensor with exchange at M, then the p2 projection.
Transpose under the composite q/p1 adjunction. Both transposes are tensor comparison
followed by a(counit_q at M) tensor b(counit_q at T); counit naturality and tensor
bifunctoriality interchange their order. Mate pasting gives equality before transposition,
with precisely pushSwap as the right comparison. Compose with the inverse p1 projection
and tensor with projectionTrace false. Its definition cancels exchange at T, leaving
pullback of the q trace. Projection naturality in the trace and its unit normalization
turn this into identity_RM tensor trace_q. Finally cancel J2, which is invertible by
Maps.projectionQ, Maps.exchange and Maps.projection2. The remaining word is unitTail
followed by epsilon. This proves the displayed equality without a diagonal insertion,
a scalar normalization, or the proposed adjunction F left adjoint G. -/
theorem towerP1FirstTraceReordering (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d)
    (M : C l E p.classes.base (ProjectiveLine S)) :
    (p.F l E).map (unitTail l E d M) ≫ epsilon l E d ((left l E d).obj M) =
      (p.pushSwap l E).hom.app
        ((SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).obj
          ((SpTowerShriek.pull l E p.classes.base
            (p.operations.geometry (pullback.fst _ _))).obj M.obj,
            (line l E p.classes.chernW)⟦(2 : ℤ)⟧)) ≫
      (p.F l E).map (contractionTail l E h false M) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerP1
