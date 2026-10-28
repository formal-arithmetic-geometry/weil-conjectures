/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Paper.FiniteRingFixedCoordinates

/-! # Open-unit normalization of the explicit finite proper/open comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- Transport of the canonical proper/open map preserves the open-adjunction transpose.
This is only the open triangle: no outer proper map or compact-support coordinate occurs.
Source: compactification-coherence proof, first paragraph; Stacks 03DI, 03D6 and 0F7B
(blueprint: lem-sf-finite-ring-fixed-open-normalization).

Proof: first work at the retained etale antecedent O.L. The proper/open map there
is the transpose of the inverse proper restriction identification. Its restriction
identification is the inverse-image compositor followed by the proper counit;
properOpenIdentification_unit gives precisely its equation with the open unit.
Transport this identity through the comparison inverse image. The extension-by-zero
comparison is the mate of the pullback comparison, and comparisonDirectImage is
its counit-normalized mate, so their unit and counit equations transport the identity.
The canonical bounded-below inclusion comparisons preserve those same derived
units and counits. This proves the equation for properOpenProEtaleIso.
Conjugate along fixedOriginWitness to obtain the equation for fixedRefinementOpen.
Finally finitePullbackIso is left-adjoint uniqueness for finiteDirectImage_eq,
and finiteOpenIso is left-adjoint uniqueness for the open adjunction after this
pullback comparison. Their unit equations identify the transported open units.
The section-normalized module compositor underlying geometricPullComposition
identifies the transported inverse-image compositor. Substitute these comparisons
and cancel their inverse pairs. The resulting map is exactly finiteFixedRefinementOpenIso
and the resulting restriction is refinementRestriction. Identity maps, empty opens,
and zero objects use the same triangle and inverse-pair identities. -/
theorem finiteFixedRefinementOpenIso_normalization
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (O : FrobeniusExchange.CompactOrigin (Padic.coefficientExtensionRing l E (n + 1)) X)
    (hi : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.i)) :
    (PurCompactSupport.openDerivedAdjunction
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.i).homEquiv _ _
        (finiteFixedRefinementOpenIso l E n r O).hom ≫
      PurCompactSupport.refinementRestriction
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) r hi O.K =
    (PurCompactSupport.openDerivedAdjunction
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c.i).unit.app O.K := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
