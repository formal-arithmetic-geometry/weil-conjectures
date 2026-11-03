/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange

/-!
# Transport of open exchange along the chosen Cartesian realization

Source: the Cartesian transport in the proof of det-prop-sf-cbc.
(blueprint: new-cbc-cartesian-open-mate-transport).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj
open AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CondensedOpenProper
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical open mate on an arbitrary Cartesian square is the literal-pullback mate
preceded by the explicitly constructed Cartesian transport.

Proof: let e be sq.isoPullback. The equations e.hom followed by the two pullback projections
are sq's two maps. Pullback compositors identify the top functors; the open compositor
identifies extension along j' with extension along e.hom and the literal pullback open.
Because e is an isomorphism, pullback along e.hom is an equivalence. Its left open adjoint has
invertible counit, and compactSupportOpenPullbackTransport is exactly contraction by that
counit after the two composition identifications. Expand the open mate on both sides into
unit, square comparison and counit. Apply naturality to move the composition identifications
past the units and counits. Pullback associativity equates the square comparisons, and the
triangle identities cancel the inserted adjunction along e.hom. This gives the equation for
exact derived pullbacks. Conjugating the top functors by the displayed exact/total derived
comparisons gives the stated equation. No base-change invertibility is used here.
Source: latest blueprint det-prop-sf-cbc, transport of the open comparison to the supplied
compactification square, and canonical mate pasting
(blueprint: new-cbc-cartesian-open-mate-transport). -/
theorem compactSupport_cartesian_open_mate_transport
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {j' : U' ⟶ Z'}
    {j : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback t j' j b) :
    ((compactSupportCondensedFormalism Λ).baseChange t j' j b sq.w).natTrans =
      (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ t) (J Λ j') ≪≫
        compactSupportOpenPullbackTransport Λ sq ≪≫
        Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.fst j b)).symm
          (J Λ (pullback.snd j b))).hom ≫
      ((compactSupportCondensedFormalism Λ).baseChange (pullback.fst j b)
        (pullback.snd j b) j b pullback.condition).natTrans := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
