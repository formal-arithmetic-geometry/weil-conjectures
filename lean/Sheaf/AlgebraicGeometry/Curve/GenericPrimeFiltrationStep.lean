/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

import Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.Curve.GenericComparison
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.NormalGenericConstant

/-! One prime-constant step of generic filtration. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.IsConnectedCurve

/-- One prime-constant step of generic filtration preserves second-cohomology
vanishing, provided the corresponding prime constant sheaf on the curve has vanishing
second cohomology.

Source: blueprint `lem-sc-affine-generic-second`, proof paragraph 3.
(blueprint: lem-sc-generic-prime-filtration-step)

Proof: apply left exact generic direct image to the short exact sequence and let I be
its image in the third term. This gives a short exact sequence from the first term to
the second term to I. The cokernel Q of I in the third term has zero generic restriction:
the counit of generic pullback/pushforward is an isomorphism and inverse image is exact.
The third term is a finite constant generic sheaf, so its direct image and Q are torsion.
Continuity at the generic point makes every section of Q vanish locally on a
nonempty affine open. Thus Q has zero positive cohomology by generic acyclicity.
The long exact sequence for
I, the third direct image, and Q identifies their second cohomology. Smoothness implies
normality; normal generic constant comparison identifies the third direct image with
the curve's constant ZMod sheaf. It has vanishing H² by hconstant. Finally the long
exact sequence for the first direct image, second direct image, and I gives the result.
This argument needs no finiteness assumption on the first two terms. -/
theorem subsingleton_generic_prime_filtration_step
    {k : Type u} [Field k] [IsAlgClosed k] {D : Scheme.{u}}
    (g : D ⟶ Spec (.of k)) [IsConnectedCurve g] [Smooth g] [IsAffine D] [IsIntegral D]
    (S : ShortComplex (Sheaf (Spec D.functionField).smallEtaleTopology
      AddCommGrpCat.{u + 1})) (hS : S.ShortExact) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (e : S.X₃ ≅ (Spec D.functionField).constantZMod ℓ)
    (hconstant : Subsingleton (Sheaf.H (D.constantZMod ℓ) 2))
    (hfirst : Subsingleton (Sheaf.H
      ((Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj S.X₁) 2)) :
    Subsingleton (Sheaf.H
      ((Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj S.X₂) 2) := by sorry

end AlgebraicGeometry.IsConnectedCurve
