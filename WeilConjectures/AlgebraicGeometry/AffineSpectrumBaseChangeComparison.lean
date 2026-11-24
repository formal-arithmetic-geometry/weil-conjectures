/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.AffineSpectrumMateCompatibility
/-! # The base-change mate in affine spectrum coordinates

## References

* Stacks Project, Tags 0DJ8, 08HY and 0D5S
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Canonical spectrum coordinate transport identifies the actual base-change
comparison followed by the given coefficient morphism. No stalk condition is used. -/
theorem affineSpectrumCoordinates_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') :
    let K0 := affineSpectrumDerivedObject X K
    let K0' := affineSpectrumDerivedObject X' K'
    let φ0 := affineSpectrumDerivedMorphism g' K K' φ
    ∃ (eL : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj K) ≅
        (derivedPullback S'.toSpecΓ).obj
          ((derivedPullback (Spec.map g.appTop)).obj
            ((schemeDerivedDirectImage (Spec.map f.appTop)).obj K0)))
      (eR : (schemeDerivedDirectImage f').obj K' ≅
        (derivedPullback S'.toSpecΓ).obj
          ((schemeDerivedDirectImage (Spec.map f'.appTop)).obj K0')),
      schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
          (schemeDerivedDirectImage f').map φ =
        eL.hom ≫ (derivedPullback S'.toSpecΓ).map
          (schemeDerivedBaseChangeMap
              (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0.w K0 ≫
            (schemeDerivedDirectImage (Spec.map f'.appTop)).map φ0) ≫ eR.inv := by
  let T := derivedPullback S'.toSpecΓ
  let R0 := schemeDerivedDirectImage (Spec.map f'.appTop)
  let a := affineSpectrumBaseChangeSourceIso f g
  let b := affineSpectrumDerivedDirectImageIso f'
  have hb := affineSpectrum_baseChange_mate_compatibility f f' g g' sq.w sq0.w K
  let eL := a.app K
  let eR := b.app K'
  refine ⟨eL, eR, ?_⟩
  apply (cancel_mono eR.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := b.hom.naturality φ
  calc
    _ = schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
        b.hom.app ((derivedPullback g').obj K) ≫
          T.map (R0.map ((derivedPullback X'.isoSpec.inv).map φ)) := by
      change schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
        ((schemeDerivedDirectImage f').map φ ≫ b.hom.app K') = _
      rw [hn]
      rfl
    _ = eL.hom ≫ T.map
        (schemeDerivedBaseChangeMap (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0.w
            (affineSpectrumDerivedObject X K) ≫
          R0.map ((affineSpectrumDerivedPullbackIso g').hom.app K)) ≫
        T.map (R0.map ((derivedPullback X'.isoSpec.inv).map φ)) := by
      rw [← Category.assoc, hb, Category.assoc]
      rfl
    _ = _ := by
      simp only [affineSpectrumDerivedMorphism, Functor.map_comp, Category.assoc]
      rfl

end AlgebraicGeometry
