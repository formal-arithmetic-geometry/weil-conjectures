/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.DiagonalTowerTraceModels

/-! # Scalar restriction and direct image of strict finite systems -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

/-- The varying direct-image square for any section-preserving residue restrictions.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
ordinary finite-coefficient direct-image comparison before right derivation.
(blueprint: lem-sfb-diagonal-trace-varying-scalar-square).

Proof: at level n, g.ordinaryPushEvaluation identifies the underlying sheaf with
evaluation on the pulled-back pro-etale chart. Its normalization is the identity
on sections, inherited from g.generic.ordinaryPushEvaluation_sections via the
specified coordinate equalities. The underlying fields of rS and rX identify the
additive groups on both sides with those same sections. Their scalar equations
make z act by the same natural-number multiple, the representative of its residue
modulo l^(n+1). Thus the normalized additive identity is Z_l-linear, with inverse
the same identity. Its naturality in the chart and in a module follows from the
restriction and morphism fields of rS and rX and naturality of ordinary evaluation.
For horizontal arrows transpose g.generic.ordinaryPullTransition through the
ordinary system and level adjunctions, using ordinary_unit_evaluation and the
adjunction triangle identities. The restrictionPullback_underlying equation identifies
this mate on underlying sheaves with the original horizontal section map.
The transitions fields of rS and rX therefore give horizontal naturality.
These equations assemble the level isomorphisms into a natural isomorphism of
strict systems, with the asserted identity on every section. No completed
coefficients or coefficient cones occur. The argument also covers identity maps,
empty sites, and level zero (the first positive quotient). -/
theorem diagonalTraceVaryingScalarSquare (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
    (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
    (rS : Restriction l (ULift.{u} (Padic l)) S)
    (rX : Restriction l (ULift.{u} (Padic l)) X) :
    ∃ e : g.push ⋙ rS.F ≅ rX.F ⋙ diagonalTraceSystemPush l f,
      ∀ (M : Systems X (Arings l (ULift.{u} (Padic l)) X)) (n : ℕ) (U : S.ProEtᵒᵖ)
        (x : (((g.push ⋙ rS.F).obj M).obj (op n)).obj.obj U),
        HEq (((e.hom.app M).app (op n)).hom.app U x) x := by sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
