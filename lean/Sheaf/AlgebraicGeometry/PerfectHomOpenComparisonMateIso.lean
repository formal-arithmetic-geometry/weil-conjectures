/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # The open direct-image mate of the fixed pullback comparison

Source: Stacks Project, Cohomology, Tags 08FE, 079W and 0D5S.
(blueprint: lem-pc-perfect-hom-open-comparison-mate-is-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The right mate of the fixed open pullback square is invertible, independently
of the testing and coefficient objects.

Source: Stacks Project, Cohomology, Lemma 20.32.4 (Tag 08FE),
Lemma 20.28.1 (Tag 079W), and Lemma 20.27.2 (Tag 0D5S).
(blueprint: lem-pc-perfect-hom-open-comparison-mate-is-iso).

Proof: Put pi = pullback.fst s r and pi' = pullback.fst (B.ι ≫ s) r.
The maps b and pi' identify B x_S T with the inverse-image open pi inverse B:
b is an open immersion, and the cartesian universal property supplies inverse
lifts between the two presentations over both Y x_S T and B. The mate is thus
a map Rpi_* followed by restriction to B -> restriction to pi inverse B followed
by Rpi'_* (with the latter restriction presented as Lb*).
For the derived adjunctions induced by the tensor-pullback adjunctions and their
specified derived comparison maps, this mate is the derived sectionwise identity
of Tag 08FE. To check its normalization, evaluate the composition comparison on
a K-flat complex: its defining left-derived counit equation is the ordinary
pullback composition comparison. Transpose by the derived adjunctions, whose
Hom equivalences on localized underived maps are pinned by the ordinary tensor
adjunction. This gives the ordinary direct-image/restriction map on complexes.
Choose a K-injective representative I of a target object. Restriction of I to
the inverse-image open is K-injective by Tag 08BS, and both complexes at an open
W of B have sections I(pi inverse W), with identical differentials. Hence the
mate component is the identity under these comparisons and is invertible.
The derived universal properties extend this identity to all derived objects.
Changing either projection adjunction conjugates its mate by the invertible
right-adjoint uniqueness comparisons. The supplied open adjunction changes
sigma by left-adjoint uniqueness; its whiskered comparison and its mate are
invertible. Thus the assertion holds for every supplied adjunction as stated.
For B empty both functors take values in the zero category; for B top the square
is the identity open square. The same calculation covers these cases and the
zero complex. No flatness, finiteness or quasi-coherence is required. -/
theorem perfect_hom_open_comparison_mate_isIso
    {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    :
    let b := pullback.map (B.ι ≫ s) r s r B.ι (𝟙 T) (𝟙 S) (by simp) (by simp)
    let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
      (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
    let he : b ≫ pullback.fst s r = pullback.fst (B.ι ≫ s) r ≫ B.ι := by
      simp [b, pullback.map]
    let κ₀ := perfectHomComposition b (pullback.fst s r) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) he) ≪≫
      (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
      Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r))
    ∀ (ap : derivedPullback (pullback.fst s r) ⊣
        schemeDerivedDirectImage (pullback.fst s r))
      (ap' : derivedPullback (pullback.fst (B.ι ≫ s) r) ⊣
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r)),
      IsIso (mateEquiv ap ap' (TwoSquare.mk _ _ _ _ κ₀.inv)).natTrans := by sorry

end AlgebraicGeometry
