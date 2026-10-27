/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData

/-! # Pasting a section comparison with an isomorphism of its ambient scheme -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Section comparisons compose with a source isomorphism over the identity base.
Source: orientation-charts Step 4, counit-preserving comparison and mate pasting.
(blueprint: lem-trf-bundle-section-comparison-iso-pasting).

Proof: expand bundleSectionComparison into the section pullback square, exceptional
base-change mate, and constant-unit comparison. Paste the square of h with the square
of a. Compact-support base-change pasting identifies the inverse exchange of the pasted
square with the composite inverse exchanges. Taking mates respects this pasting, by
mateEquiv_vcomp and the conjugate-equivalence identity law. Pullback compositor
associativity identifies the two section pullback squares. Naturality moves the unit
comparison through the exceptional functor; constant-unit pullback composition then
identifies the two unit comparisons with the one for v. The pullback identity unitor
cancels the comparison for the identity base. The remaining component equation is the
one displayed below. This concerns arbitrary section objects and squares, without any
Tate coefficients, affine frames, purity or normalized orientations. In particular it
also applies when the schemes are empty or the coefficient ring is zero.
-/
theorem bundleSectionComparison_iso_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U W S T : Scheme.{u}} (p : X ⟶ S) (q : U ⟶ S) (r : W ⟶ T)
    [HasCompactification p] [HasCompactification q] [HasCompactification r]
    [QuasiCompact q] [QuasiCompact r]
    (h : U ≅ X) (hp : h.hom ≫ p = q) (v : T ⟶ S) (a : W ⟶ U)
    (sq : IsPullback a r q v) (sq' : IsPullback (a ≫ h.hom) r p v)
    (z : S ⟶ X) (w : S ⟶ U) (b : T ⟶ W) (hz : w ≫ h.hom = z)
    (hw : b ≫ a = v ≫ w) (hw' : b ≫ (a ≫ h.hom) = v ≫ z) :
    (ordinaryFinitePullback A v).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app
            ((ordinaryFinitePullback A z).obj
              ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) p).obj
                (ordinaryFiniteUnit A S))) ≫
          bundleSectionComparison A p q h.hom (𝟙 S)
            (IsPullback.of_horiz_isIso
              (CommSq.mk (hp.trans (Category.comp_id _).symm)))
            z w (hz.trans (Category.id_comp _).symm)) ≫
        bundleSectionComparison A q r a v sq w b hw =
      bundleSectionComparison A p r (a ≫ h.hom) v sq' z b hw' := by sorry

end AlgebraicGeometry.Etale
