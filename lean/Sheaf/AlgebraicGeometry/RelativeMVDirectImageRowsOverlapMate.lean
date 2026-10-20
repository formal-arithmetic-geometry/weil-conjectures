/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Sheaf.AlgebraicGeometry.MayerVietorisImageChainData

/-! # The overlap mate for resolved relative rows -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Cancellation of the overlap component of a resolved relative row comparison.
Source: the resolved overlap mate in Stacks Project, Cohomology of Sheaves,
Tags 08BV, 08HZ, 08FE and 08HY.
(blueprint: lem-pc-relative-mv-direct-image-rows-overlap-mate).

Proof: postcompose the pre-cancellation overlap mate with the target vertex
isomorphism and simplify using its inverse-hom identity. -/
theorem relativeMV_direct_image_rows_overlap_mate
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (P : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ))
    (P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
    (m : P ⟶ P'.map
      ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)))
    (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₃) ≅
      (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).left)
    (e₃' : DerivedCategory.Q.obj P'.X₃ ≅
      (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).right)
    (h₃ : ((relativeMVAdj g).homEquiv _ _).symm (DerivedCategory.Q.map m.τ₃ ≫
      (schemeMVDirectImageLocalization g).app P'.X₃) =
        e₃.hom ≫ (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).hom ≫ e₃'.inv) :
    ((relativeMVAdj g).homEquiv _ _).symm
      (DerivedCategory.Q.map m.τ₃ ≫ (schemeMVDirectImageLocalization g).app P'.X₃) ≫
        e₃'.hom = e₃.hom ≫
          (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).hom := by
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun k => k ≫ e₃'.hom) h₃

end AlgebraicGeometry
