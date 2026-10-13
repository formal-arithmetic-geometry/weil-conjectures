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

/-- The first part of the target transpose: compute the composite base change and
its f-counit, leaving the single open-square base change and target open counit intact.
Source: Stacks Project, Cohomology, Tags 08HY, 08HZ and 0D5S.
(blueprint: new-relative-mv-composite-base-change-counit).
Proof: Expand relativeMVLocalArrow and relativeMVRestriction. Naturality of the
composite-adjunction Hom equivalence and the defining mate equation of
relativeMVImageComp remove the target direct-image comparisons. The transpose
is the transpose of the U local arrow under the f'-adjunction, pulled back along
W' → X', followed by the explicit open restriction counit defined using c'.
Expand base change for U → X → S using 08HY, and replace the inverse U,f
right-adjoint comparison by its defining mate equation. The counit of the
composite adjunction is the pullback of the f-counit followed by the U-counit.
Naturality moves the U coefficient comparison through the transpose; the triangle
identity cancels the intermediate f'-unit. The remaining U-counit and square
comparison are precisely base change for U → X followed by the U coefficient
comparison. Associativity of relativeMVComp for W → X → S and for the two
base-change squares identifies the preceding factors with the W square comparison,
the pulled-back inverse W,f comparison and f-counit, and the W coefficient
comparison at C. Projection identities and hpull.w identify the scheme composites;
proof irrelevance identifies the equality transports. Leave the trailing c' and
open restriction counit unchanged: their calculation is a separate identity.
Equal and empty opens and zero complexes require no special assumptions, since
only functoriality, naturality, coherence and adjunction identities were used. -/
theorem relativeMV_composite_baseChange_counit
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
      (relativeMVComp (pullback.fst g' W.ι ≫ f') g).hom.app A ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A)
        (show pullback.snd g' W.ι ≫ (W.ι ≫ f) =
            (pullback.fst g' W.ι ≫ f') ≫ g by
          rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]).symm) ≫
      (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).inv.app A ≫
      (derivedPullback (pullback.snd g' W.ι)).map
        ((relativeMVComp W.ι f).inv.app A ≫
          (derivedPullback W.ι).map
            ((derivedPullback f).map ((relativeMVImageComp U.ι f).inv.app
                ((derivedPullback U.ι).obj K)) ≫ (relativeMVAdj f).counit.app C)) ≫
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app C ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj C)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app C ≫
      (derivedPullback (pullback.fst g' W.ι)).map
        (schemeDerivedBaseChangeMap U.ι (pullback.fst g' U.ι) g'
            (pullback.snd g' U.ι) (pullback.condition (f := g') (g := U.ι)).symm
            ((derivedPullback U.ι).obj K) ≫
          (schemeDerivedDirectImage (pullback.fst g' U.ι)).map θ) ≫
      c'.inv.app ((schemeDerivedDirectImage (pullback.fst g' U.ι)).obj
        ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      (derivedPullback (relativeMVOpenLift g' i)).map
        ((relativeMVAdj (pullback.fst g' U.ι)).counit.app
          ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      c'.hom.app ((derivedPullback g').obj K) := by sorry

end AlgebraicGeometry
