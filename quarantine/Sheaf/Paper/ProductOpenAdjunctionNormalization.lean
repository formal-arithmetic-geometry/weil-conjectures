/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.ProductExchangeCoordinateDefinitions

/-! # Open adjunction normalization in product coordinates

Source: Stacks 09BN and the counit calculation in the symmetry paragraph of
lem-sf-kunneth-coherence.proof.md
(blueprint: lem-pur-product-open-adjunction-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.ProductExchangeCoordinates

/-- The sectionwise restriction is the actual exchange, and its inverse-open-unit
normalization agrees with the actual proper/open mate and open counit.
Source: Stacks 09BN, open localization; product-coordinate node Steps 3, 5 and 6
(blueprint: lem-pur-product-open-adjunction-normalization).

Proof: on a K-injective complex the restriction map evaluates a section on the
canonical pullback object. Its transpose under inverse image/direct image evaluates
the same section, so it is the specified exchange. In the Cartesian square the
clopen intermediate lift is an isomorphism. Restrict the clopen-projection definition
of the proper/open mate, paste its two proper adjunctions, and use their triangle
identities. The result is the inverse of restriction followed by inverse open unit,
which is exactly the inverse of lambda. Finally naturality of restriction at the
open counit and the triangle identity identify restriction of that counit with
inverse open unit; this gives the last equality. The calculation is on arbitrary
unbounded objects and inverts only open units and sectionwise restriction. -/
theorem productOpenAdjunctionNormalization
    {B X Z : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
    (cf : Compactification f) (cg : Compactification g) [QuasiCompact g]
    (A : Type u) [CommRing A] [Finite A]
    (Q : ProperOpenDerived (ULift.{u + 1} A) (pullback cf.g cg.g)) :
    (rho A (pullback.snd cf.g g) (i cf cg) cg.i
      (pullback.snd cf.g cg.g) (square cf cg)).hom.app Q =
        (derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (square cf cg).flip.toCommSq).app Q ∧
    (properOpenAdj (ULift.{u + 1} A) cg.i).homEquiv _ _
      ((properOpenMate (ULift.{u + 1} A) (i cf cg) (pullback.snd cf.g g)
        (pullback.snd cf.g cg.g) cg.i (comm cf cg)).app
          ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj Q)) =
      (lambda cf cg A ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj Q)).inv ∧
    (ProperOpenPull (ULift.{u + 1} A) cg.i).map
        ((ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g)).map
          ((properOpenAdj (ULift.{u + 1} A) (i cf cg)).counit.app Q)) ≫
      (rho A (pullback.snd cf.g g) (i cf cg) cg.i
        (pullback.snd cf.g cg.g) (square cf cg)).hom.app Q =
      (lambda cf cg A ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj Q)).hom := by sorry

end AlgebraicGeometry.ProEtale.ProductExchangeCoordinates
