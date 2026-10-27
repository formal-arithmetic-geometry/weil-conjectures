/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.TowerP1TriangleWords

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

/-- The diagonal-free second trace rearrangement, specialized only to N=GK.
No diagonal insertion or integral appears in this identity of maps out of Rp2*(p1*N tensor T_W).

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction, second triangle; steps 6--8 of the parent node
(blueprint: lem-sp-tower-p1-second-trace-reordering).

Proof: put N=q*K tensor T. Apply exchange/tensor coherence to the q square at inside
T and outside K. It equates exchange_N after pullback of projection_q(K,T) with
projection_p2(q*K,p1*T) after identity tensor exchange_T. All these comparisons
are invertible on the domains supplied by Maps and EtaleOriginComparisonsWithLine;
invert the equation. Tensor associativity for projection extracts the last T in
unitTail_N. The comparison rightPullComparison is exactly the square on q*K
and line1Iso followed by inverse line2Iso on its T factor. The two copies of the
unshifted Tate line have identity self-symmetry: on a common root frame multiplication
rs equals sr, and the equation is invariant under change of frame. Moving [2] past
degree j contributes (-1)^(2j)=1, and swapping its two copies contributes (-1)^4=1,
also when ell=2. Thus the extracted word is pullback(projection_q) tensor identity,
followed by inverse exchange_T and the swap of the two line factors. On composing
with G(epsilon_K), the adjacent projection and its inverse cancel. By the definition
of projectionTrace true the remaining inverse exchange followed by pulled trace is
the projection trace; symmetry naturality for this trace and the unitors moves it
to the last factor. The resulting word is precisely contractionTail true after the
pushed tensor of rightPullComparison. No equality of general derived maps is inferred
from their level evaluations. -/
theorem towerP1SecondTraceReordering (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d)
    (K : C l E p.classes.base S) :
    unitTail l E d ((rightRestricted l E d).obj K) ≫
        (p.G l E).map (epsilon l E d K) =
      (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (pullback.snd _ _))).map
          ((SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).map
            (Prod.mkHom (rightPullComparison l E p K.obj).hom (𝟙 _))) ≫
      contractionTail l E h true ((rightRestricted l E d).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerP1
