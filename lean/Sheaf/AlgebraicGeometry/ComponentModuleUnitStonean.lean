/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.AlgebraicGeometry.GenericComponentData
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.RingTheory.ProEtale.WContractible

/-!
# The component module unit on Stonean tests

Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), proof;
Stacks Project, Modules on Sites, Tags 03D2, 03D3 and 03D7.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The component module unit is bijective on every extremally disconnected test.
The coefficient is any ring sheaf on the profinite slice, and its inverse image is
identified with the scheme coefficient by the specified isomorphism. The scalar map
is the adjunct of that isomorphism. No finite-limit or exactness assumption on the
module functors is imposed.

Source: HRS Proposition 4.3(1), proof; BS Lemmas 2.2.8, 2.4.8, 4.2.13(1);
Stacks Tags 00VE, 00WX, 03D2, 03D3 and 03D7.
(blueprint: lem-sfb-component-module-unit-stonean).

Proof: Write U(D)=W_D. For an extremally disconnected E the component-site
geometry identifies W_E with |W| times over pi_0(W) E and its stalks with those
of W. Its closed points are exactly the pairs with closed first coordinate.
The w-local and strict-local conditions therefore pass from W to W_E, and its
component quotient is E, so W_E is w-contractible. The clopen partition theorem
splits every finite qcqs cover of W_E: glue the local lifts into the coproduct of
the covering members. Split-cover evaluation consequently computes sheaf inverse
image at W_E without changing the Kan-extension value.

A W-map W_E to W_D determines a continuous map E to D over pi_0(W), by the
component quotient. Conversely that map gives a continuous map of the pullback
spaces; the stalk-isomorphism lifting theorem gives its unique scheme lift.
Thus (E,id) is initial among pairs (D,W_E to W_D), and terminal after taking
opposites. The inverse-image Kan colimit is A(E), with identity coprojection.
The sheaf adjunction unit is precisely this coprojection followed by
sheafification, hence is identity under split-cover evaluation.

Apply the same calculation to the ring, the underlying additive sheaf of a
module, and its scalar action. Finite-product comparisons transport all operations.
The module inverse-image adjunction has the underlying sheaf transpose, by
Tags 03D2 and 03D3. Changing the inverse-image ring along c gives the specified
Mathlib pushforward with scalar map adj.unit followed by pushforward(c).
Extension along c is an equivalence: its inverse on tensors is b tensor m
mapped to c inverse(b) times m, with inverse m mapped to 1 tensor m.
Thus the module unit at E is the identity in this calculation and is bijective.
Uniqueness of left adjoints transports this result to Mathlib's chosen pullback
and unit. The statement is invariant under the resulting unit-compatible
isomorphism. Empty E and empty W give zero module sections by the empty cover
condition, so the same calculation includes them. -/
theorem component_module_unit_bijective_on_stonean_tests
    (W : Scheme.{u}) [IsAffine W] [IsWContractibleRing Γ(W, ⊤)]
    (A : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite W)) RingCat.{u + 1})
    (B : Sheaf (topology W) RingCat.{u + 1})
    (L : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite W)) RingCat.{u + 1}
      ⥤ Sheaf (topology W) RingCat.{u + 1})
    (adj : L ⊣ genericComponentRingPush W) (c : L.obj A ≅ B)
    [(SheafOfModules.pushforward.{u + 1}
      (adj.unit.app A ≫ (genericComponentRingPush W).map c.hom)).IsRightAdjoint]
    (E : Over (componentProfinite W)) [ExtremallyDisconnected E.left]
    (M : SheafOfModules.{u + 1} A) :
    Function.Bijective
      (((SheafOfModules.pullbackPushforwardAdjunction
        (adj.unit.app A ≫ (genericComponentRingPush W).map c.hom)).unit.app M).val.app
          (op E)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
