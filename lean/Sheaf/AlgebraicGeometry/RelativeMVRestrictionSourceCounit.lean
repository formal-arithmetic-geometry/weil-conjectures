/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps

/-! # A counit normal form for the relative restriction square

Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 08HZ.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- The source path has the explicit restricted-counit normal form.
Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 08HZ.
(blueprint: new-relative-mv-restriction-source-counit).
Proof: Transpose only the source path under L(W'→S') adjoint to R(W'→S').
Functoriality of the Hom equivalence moves Lg(restriction) to the left of the
base-change transpose and the coefficient comparison to its right. By 08HY,
the base-change transpose is the pullback square comparison followed by
L(W'→W) of the counit for W→S. Naturality of the square comparison moves
restriction inside this pullback. Expand relativeMVRestriction. The mate
identity for relativeMVImageComp W.ι f replaces its last factor by the counit
of the composite adjunction, precomposed with (relativeMVComp W.ι f).inv.
Naturality moves the initial direct-image comparison through that inverse
pullback comparison. The composite counit is L(W→X) of the counit for f,
followed by the counit for W→X. The triangle identity cancels the Hom-equivalence
transpose defining the middle factor of restriction. What remains is precisely
the displayed pullback of the two restricted counits, followed by the W
coefficient comparison. No triple-composition coherence and no target path
are used in this calculation. Equal and empty opens satisfy the same identities. -/
theorem relativeMV_restriction_source_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (W U : X.Opens) (i : W ≤ U) :
    let A := (schemeDerivedDirectImage (U.ι ≫ f)).obj ((derivedPullback U.ι).obj K)
    let c := relativeMVComp (X.homOfLE i) U.ι ≪≫
      eqToIso (congrArg (fun t : W.toScheme ⟶ X ↦ derivedPullback t)
        (Scheme.homOfLE_ι X i))
    let t := (relativeMVComp (pullback.fst g' W.ι ≫ f') g).hom.app A ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A)
        (show pullback.snd g' W.ι ≫ (W.ι ≫ f) =
            (pullback.fst g' W.ι ≫ f') ≫ g by
          rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]).symm) ≫
      (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).inv.app A ≫
      (derivedPullback (pullback.snd g' W.ι)).map
        ((relativeMVComp W.ι f).inv.app A ≫
          (derivedPullback W.ι).map
            ((derivedPullback f).map
                ((relativeMVImageComp U.ι f).inv.app ((derivedPullback U.ι).obj K)) ≫
              (relativeMVAdj f).counit.app
                ((schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K))) ≫
          c.inv.app ((schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)) ≫
          (derivedPullback (X.homOfLE i)).map
            ((relativeMVAdj U.ι).counit.app ((derivedPullback U.ι).obj K)) ≫
          c.hom.app K) ≫
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app K
    ((relativeMVAdj (pullback.fst g' W.ι ≫ f')).homEquiv _ _).symm
      ((derivedPullback g).map
          (relativeMVRestriction (X.homOfLE i) U.ι W.ι (Scheme.homOfLE_ι X i) f K) ≫
        (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
          (𝟙 _) W).hom) = t := by
  sorry

end AlgebraicGeometry
