/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Curve.Brauer
import WeilConjectures.AlgebraicGeometry.Curve.Kummer
import Sheaf.AlgebraicGeometry.GmPicardPullback
import WeilConjectures.AlgebraicGeometry.Picard.Scheme
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# Geometric faithfulness of odd abelian level on curves

Source: Pikaart--de Jong, Moduli of curves with non-abelian level structure,
Sections 1.1(1) and 2.3.3 (blueprint: lem-sfb-geometric-curve-level-faithfulness).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An automorphism over an algebraically closed field of a smooth projective connected
curve of genus at least two is the identity if it fixes first étale cohomology modulo a
prime at least three distinct from the characteristic. The coefficient comparison is the
canonical pullback isomorphism of constant sheaves, so the hypothesis is the actual
endomorphism of cohomology with constant coefficients.

Source: Pikaart--de Jong, Sections 1.1(1) and 2.3.3; Milne, Abelian Varieties,
I Proposition 14.4(b), III Section 6 and Theorem 12.1(b)
(blueprint: lem-sfb-geometric-curve-level-faithfulness).

Proof:
1. Choose a primitive ell-th root by lem-sc-primitive-root. The trivialization
   def-sc-mu-trivialization commutes with the curve automorphism over the field and its coefficient
   comparison. Naturality lem-weil-pbc-cohomology-pullback-functorial transfers the trivial
   action to H¹ of the roots-of-unity sheaf.
2. By lem-kun-projective-implies-proper the curve is proper. Its global functions are the
   base field by lem-sc-global-functions, so its units are ell-divisible. Together with
   lem-sc-brauer-zero, lem-sc-kummer-les identifies this H¹ with ell-torsion in Pic.
   Naturality of the Kummer inclusion and lem-sc-h1-gm-pic-pullback identify the action
   there with pullback of line bundles. Thus all ell-torsion classes are fixed.
3. Choose the Jacobian by sk-thm-picard-main. The pullback automorphism and canonical
   principal polarization are supplied by lem-sfb-curve-polarized-jacobian-faithfulness.
   By det-cor-jacobian-torsion-pic(2), its ell-torsion points are precisely Pic[ell],
   and hence are fixed; the automorphism also preserves the polarization.
4. Apply lem-sfb-polarized-abelian-odd-level-rigidity: ell is invertible in the field,
   ell is at least three, and the polarized Jacobian automorphism fixes its ell-torsion.
   Consequently that automorphism is the identity.
5. The injectivity assertion of lem-sfb-curve-polarized-jacobian-faithfulness, using
   genus at least two, implies that the original curve automorphism is the identity. -/
theorem geometric_curve_level_faithfulness
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of Ω)) [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (hgenus : 2 ≤ f.genus) (ℓ : ℕ) (hprime : ℓ.Prime) (hlevel : 3 ≤ ℓ)
    (hchar : (ℓ : Ω) ≠ 0) (a : C ≅ C) (hover : a.hom ≫ f = f)
    (hacts : ∀ x : Sheaf.H (C.constantZMod ℓ) 1,
      Sheaf.H.map
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} a.hom).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) 1
        (Etale.cohomologyMap a.hom (C.constantZMod ℓ) 1 x) = x) :
    a = Iso.refl C := by
  sorry

end AlgebraicGeometry
