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

/-- The composite base-change transpose before applying the target open counit.
Source: Stacks Project, Cohomology, Tags 08HY, 08HZ and 0D5S.
(blueprint: new-relative-mv-composite-base-change-prefix).
Proof: Expand the U local arrow. The mate equation for the inverse U,f direct-image
comparison and naturality of the composite adjunction counit express its f'-transpose
as base change for f, followed by base change for U and the U coefficient comparison.
The composite counit formula pulls the f counit through the U comparison; triangle
identities cancel the intermediate f'-unit. Pull this formula back along W' to X'.
Apply associativity coherence of the canonical pullback comparisons to W→X→S and
the corresponding pullback squares. The projection identities and hpull.w identify
all composite scheme morphisms, and proof irrelevance identifies transports. This
leaves exactly the W square comparison and pulled-back f counit, the W coefficient
comparison at C, and the pulled-back U base-change arrow. No counit for U'→X'
is computed or applied. All identities include equal and empty opens and zero
complexes, since they are natural transformations and coherence identities. -/
theorem relativeMV_composite_baseChange_prefix
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (W U : X.Opens) :
    let C := (schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)
    let A := (schemeDerivedDirectImage (U.ι ≫ f)).obj ((derivedPullback U.ι).obj K)
    let θ := (relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' U.ι) g').inv.app K
    (relativeMVComp (pullback.fst g' W.ι) f').inv.app
      (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) U).left ≫
      (derivedPullback (pullback.fst g' W.ι)).map
        (((relativeMVAdj f').homEquiv _ _).symm
          ((relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
              (𝟙 _) U).hom ≫
            (relativeMVImageComp (pullback.fst g' U.ι) f').inv.app
              ((derivedPullback (pullback.fst g' U.ι)).obj
                ((derivedPullback g').obj K)))) =
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
          (schemeDerivedDirectImage (pullback.fst g' U.ι)).map θ) := by sorry

end AlgebraicGeometry
