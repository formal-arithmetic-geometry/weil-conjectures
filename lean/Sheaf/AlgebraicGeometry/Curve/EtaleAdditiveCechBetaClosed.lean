/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization

/-! # Coefficient augmentation preserves closed elements
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The coefficient augmentation sends cycles to elements killed by the total differential.
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2, augmentation beta.
(blueprint: lem-pbc-etale-additive-cech-beta-closed)

Proof: Identify the unit module on each finite open intersection with its additive
structural sections using restrictFunctorGamma and lift by ULift. Naturality of
this identification and of the resolution augmentation identifies the horizontal
differential of beta(z) with beta of the coefficient differential of z, hence zero.
The vertical differential is zero because the resolution augmentation is killed
by its first differential. The total differential is the sum of these two
components, with the standard sign on the vertical component, so it vanishes.
The argument applies in degree zero and to empty or repeated intersections; it
does not require a covering or an affine acyclicity hypothesis. -/
theorem etaleAdditiveCech_beta_closed
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n) :
    (additiveCechTotal U I).d n (n + 1)
      (additiveCechBeta U I n
        ((cechOver X.toSpecΓ U
          (SheafOfModules.unit X.ringCatSheaf)).iCycles n z)) = 0 := by sorry

end AlgebraicGeometry.Scheme.Modules
