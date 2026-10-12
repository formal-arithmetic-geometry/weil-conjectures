/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-! # Finite-open transfer for prime module coefficients

Source: Stacks Project, etale-cohomology.tex, 0A5D and 0GJ1.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- Transfer assertions across a finite-open square, allowing a supplied
isomorphism of the sheaf on the upper open. No filtration or constant-case
hypothesis is part of this result.

Source: Stacks Project 0A5D (lemma-finite-pushforward-statements) and
0GJ1 (lemma-compatible-shriek-push-finite).
(blueprint: r1-prime-module-finite-open-assertions-transfer)

Proof: Apply a_! to e and transport the eight assertions to a_! H. Finite
pushforward preserves them: its cohomology comparison is an isomorphism in
all degrees, since finite pushforward has no positive derived functors.
For C2 a finite scheme over an affine is affine; for C5 and C7 a finite
scheme over a proper scheme is proper. The torsion conditions in C3 and C6
pass from p_* a_! H to a_! H by the finite stalk formula, a finite product
of geometric stalks. Constructibility passes in the same direction when
needed for C4 and C5. Finite base change makes the cohomology comparisons
commute with field extension and restriction to opens, giving C6--C8.
All sheaves are r-torsion because the coefficient ring has characteristic r.
Finally the finite-open exchange identifies p_* a_! H with j_! v_* H,
and its naturality transports all eight assertions to the latter sheaf.
This includes zero sheaves and empty opens and does not require surjectivity. -/
theorem prime_module_finite_open_assertions_transfer
    {k : Type u} [Field k] [IsAlgClosed k] {X U V Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (p : Y ⟶ X) [IsFinite p]
    [IsCurve (p ≫ f)] (j : U ⟶ X) [IsOpenImmersion j]
    (a : V ⟶ Y) [IsOpenImmersion a] (v : V ⟶ U) (sq : IsPullback a v p j)
    (r : ℕ) [Fact r.Prime]
    (F H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (e : F ≅ H)
    (hF : Assertions (ULift.{u + 1} (ZMod r)) (p ≫ f)
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
        F)) :
    Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj H)) := by sorry

end AlgebraicGeometry.IsCurve
