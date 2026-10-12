/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion
import WeilConjectures.AlgebraicGeometry.Curve.Brauer
import WeilConjectures.AlgebraicGeometry.Curve.Kummer
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Étale cohomology of a smooth proper connected curve

Source: Stacks Project, Tag 03RQ, Lemma 59.69.1, with higher vanishing from Tag 03RT;
blueprint sec-curve-estimates/sk-thm-curveestimate (blueprint: thm-sc-proper-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The Kummer computation for a smooth proper connected curve over an algebraically closed
field: constant `ZMod n` coefficients give `ZMod n` in degrees zero and two, a product of
`2 * f.genus` copies in degree one, and zero in every higher degree.
Source: Stacks Project, Tag 03RQ, Lemma 59.69.1 (blueprint: thm-sc-proper-cohomology).

Proof for stage 3:
1. Choose a primitive root by lem-sc-primitive-root. The sheaf isomorphism
   `Scheme.constantZModIsoRootsOfUnitySheaf` of def-sc-mu-trivialization transports cohomology
   from the constant sheaf to the roots-of-unity sheaf. These identifications are noncanonical.
2. Smoothness gives reducedness. Properness and connectedness identify global units with
   those of the base field, whose n-th power map is surjective. Apply lem-sc-kummer-les and
   lem-sc-brauer-zero: degree one is Picard n-torsion, degree two is the Picard cokernel of n,
   and degree zero is the group of n-th roots of unity in the base field.
3. Apply lem-sc-pic-proper-ntorsion to identify the torsion with `2 * f.genus` copies of
   `ZMod n` and the cokernel with `ZMod n`; the primitive root identifies degree zero too.
   Transport these computations along the trivialization from step 1.
4. The constant sheaf is torsion. Apply lem-sc-cohomological-dimension to the smooth separated
   connected curve of def-sc-curves to obtain vanishing in all degrees greater than two. -/
theorem IsConnectedCurve.sheafH_constantZMod_of_isProper
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * f.genus) → ZMod n)) ∧
      Nonempty (Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n) ∧
      ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H (C.constantZMod n) q) := by
  sorry

end AlgebraicGeometry
