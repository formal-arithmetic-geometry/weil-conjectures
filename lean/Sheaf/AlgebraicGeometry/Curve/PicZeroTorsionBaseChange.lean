/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible
import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Degree-zero Picard points under algebraically closed field extension

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance, proper case and the
Jacobian point comparison in the affine case (blueprint: lem-sc-piczero-torsion-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false

/-- The canonical comparison on degree-zero Picard groups is injective and every
prime-to-characteristic torsion point after extension lifts to a torsion point before extension.

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance, proper degree-one comparison
and affine Jacobian correction (blueprint: lem-sc-piczero-torsion-base-change).

Proof: a proper smooth connected curve over an algebraically closed field is geometrically
integral and smooth of relative dimension one. Jacobian representability identifies its
Picard degree-zero subgroup with the rational points of its Jacobian. Compatibility of the
representing Picard functor with base change identifies the specified pullback homomorphism
with extension of rational points of this same Jacobian. The latter is injective: two
morphisms from Spec k equal after Spec k' have the same image point and the same residue-field
map, since k to k' is injective. For torsion, n is positive and prime to the characteristic,
so clause (c) of the abelian-variety estimate makes extension bijective on the rational
points of the finite etale n-torsion subgroup scheme. Identify those points with the elements
whose nth power is one, and transport through the natural Jacobian identifications. The
hypotheses on G, G', and j merely choose subgroup models and spell out that canonical map.
For n=1 torsion consists of the identity; for a genus-zero curve both groups are trivial.
The conclusion does not assert anything about an affine quotient or a boundary subgroup. -/
theorem picZero_torsion_base_change
    {k k' : Type u} [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f]
    (G : Subgroup X.Pic) (hG : (G : Set X.Pic) = f.picZero)
    (G' : Subgroup (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic)
    (hG' : (G' : Set (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic) =
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).picZero)
    (j : G →* G')
    (hj : ∀ L : G, (j L).val = Scheme.Pic.mapHom
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L.val)
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Function.Injective j ∧ ∀ y : G', y ^ n = 1 → ∃ x : G, x ^ n = 1 ∧ j x = y := by sorry

end AlgebraicGeometry
