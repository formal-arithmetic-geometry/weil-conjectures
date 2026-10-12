/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Constant prime coefficients extended by zero on reduced curves

Source: Stacks Project, Lemmas 03SG (lemma-even-easier) and 0A3Q
(lemma-somewhat-easier).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- Constant prime coefficients extended by zero on a reduced curve.

Source: Stacks Project, 03SG (lemma-even-easier), 0A3Q (lemma-somewhat-easier),
0A5B (lemma-constant-smooth-statements), 0GJA (lemma-restrict-to-open).
(blueprint: k1-reduced-constant-lower-shriek-assertions)

Proof:
1. On a smooth curve, split into its finitely many disjoint irreducible components.
Smooth local rings are domains, so distinct components cannot intersect; Noetherianity
makes the components open as well as closed. On each component an open is either empty
or dense. The empty case has zero extension by zero. In the dense case apply the
Kummer calculations if r is invertible in k and the Artin--Schreier calculations
otherwise (0A5B), followed by dense-open localization (0GJA). Finite pushforward from
components and short-exact devissage reassemble their finite direct sum (03SG).
Points are included: their positive cohomology vanishes and degree zero is the stalk.
2. For a reduced curve choose the finite smooth modification nu : Xn -> X,
isomorphic over a dense open D, supplied by reduced-curve normalization. Pull j back
to jn on Xn. Step 1 gives the assertions for jn_! R; finite pushforward (0A5D,
lemma-finite-pushforward) gives them for nu_* jn_! R.
3. Both nu_* jn_! R and j_! R are constructible: the latter is constant on U and
zero on its complement, and finite pushforward preserves constructibility. Over D
they agree, because nu is an isomorphism there and the stalk description of extension
by zero commutes with restriction to opens. Apply 0GJA twice to transfer the assertions
between these two sheaves (0A3Q).
4. All sheaves have their canonical R = ULift(ZMod r) module structure. The constant
sheaf R is the constant prime-field sheaf used in the cited calculations, since r = 0
in R. Forgetting modules preserves the stalk formulas and the cohomology comparison
maps, so this proves the stated module-valued assertion package. -/
theorem reducedConstantLowerShriekAssertions {k : Type u} [Field k] [IsAlgClosed k]
    {X U : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime] :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        ((constantSheaf U.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod r))))) := by sorry

end AlgebraicGeometry.IsCurve
