/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps

/-! # The counit for base change of a composite morphism

Source: Stacks Project, Cohomology, Tags 08HY, 08HZ and 0D5S.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Transposing the target restriction removes the direct-image composition mates.
Source: Stacks Project, Cohomology, Tags 08HY, 08HZ and 0D5S.
(blueprint: new-relative-mv-composite-base-change-target-transpose).
Proof: Expand relativeMVRestriction. Its three factors are the inverse U',f'
right-adjoint comparison, Rf' applied to the adjoint of the restricted open counit,
and the W',f' right-adjoint comparison. Naturality in the source of the adjunction
Hom equivalence moves the incoming local arrow and inverse U',f' comparison
through the transpose. The mate identity for the final W',f' comparison replaces
its composite counit by the inverse pullback composition comparison followed by
L(W'→X') of the f' counit and then the W' counit. Naturality moves the middle
Rf' map through the f' counit. The triangle identity cancels the transpose of
the restricted open counit. Naturality of the inverse pullback comparison then
moves the incoming arrow to the f' transpose. The remaining three factors are
exactly the inverse c', pulled-back U' counit, and c' at Lg'K shown below.
The base-change map in the local arrow is neither expanded nor computed.
This argument uses only adjunction naturality and the mate counit identity, so
equal opens, empty opens and zero objects satisfy it without extra hypotheses. -/
theorem relativeMV_composite_baseChange_target_transpose
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (W U : X.Opens) (i : W ≤ U) :
    let C := (schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)
    let A := (schemeDerivedDirectImage (U.ι ≫ f)).obj ((derivedPullback U.ι).obj K)
    let c' := relativeMVComp (relativeMVOpenLift g' i) (pullback.fst g' U.ι) ≪≫
      eqToIso (congrArg (fun t : pullback g' W.ι ⟶ X' ↦ derivedPullback t)
        (pullback.lift_fst _ _ _))
    let θ := (relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' U.ι) g').inv.app K
    ((relativeMVAdj (pullback.fst g' W.ι ≫ f')).homEquiv _ _).symm
      ((relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
          (𝟙 _) U).hom ≫
        relativeMVRestriction (relativeMVOpenLift g' i) (pullback.fst g' U.ι)
          (pullback.fst g' W.ι) (pullback.lift_fst _ _ _) f'
          ((derivedPullback g').obj K)) =
    (relativeMVComp (pullback.fst g' W.ι) f').inv.app
      (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) U).left ≫
      (derivedPullback (pullback.fst g' W.ι)).map
        (((relativeMVAdj f').homEquiv _ _).symm
          ((relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
              (𝟙 _) U).hom ≫
            (relativeMVImageComp (pullback.fst g' U.ι) f').inv.app
              ((derivedPullback (pullback.fst g' U.ι)).obj
                ((derivedPullback g').obj K)))) ≫
      c'.inv.app ((schemeDerivedDirectImage (pullback.fst g' U.ι)).obj
        ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      (derivedPullback (relativeMVOpenLift g' i)).map
        ((relativeMVAdj (pullback.fst g' U.ι)).counit.app
          ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      c'.hom.app ((derivedPullback g').obj K) := by sorry

end AlgebraicGeometry
