/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.AffineSpectrumStalkCondition
import WeilConjectures.AlgebraicGeometry.AffineSpectrumBaseChangeComparison
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Spectrum coordinates for a single-complex affine square

## References

* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Transport an affine square to the spectra of its global section rings.
This statement concerns coordinate transport, not invertibility of the comparison.
The two displayed isomorphisms identify its endpoints and the final equation
identifies the actual morphism, including its given coefficient map.
 Canonical transport details expanded by C1. -/
theorem exists_singleComplexAffineSpectrumCoordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K') :
    let f0 := Spec.map f.appTop
    let f0' := Spec.map f'.appTop
    let g0 := Spec.map g.appTop
    let g0' := Spec.map g'.appTop
    ∃ (K0 : schemeDerivedCategory (Spec Γ(X, ⊤)))
      (K0' : schemeDerivedCategory (Spec Γ(X', ⊤)))
      (φ0 : (derivedPullback g0').obj K0 ⟶ K0'),
      schemeDerivedQCohProperty (Spec Γ(X, ⊤)) K0 ∧
      schemeDerivedQCohProperty (Spec Γ(X', ⊤)) K0' ∧
      (SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ ↔
        SingleComplexBaseChange.StalkCondition f0 f0' g0 g0' sq0 K0 K0' φ0) ∧
      ∃ (eL : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj K) ≅
          (derivedPullback S'.toSpecΓ).obj
            ((derivedPullback g0).obj ((schemeDerivedDirectImage f0).obj K0)))
        (eR : (schemeDerivedDirectImage f').obj K' ≅
          (derivedPullback S'.toSpecΓ).obj ((schemeDerivedDirectImage f0').obj K0')),
        schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
            (schemeDerivedDirectImage f').map φ =
          eL.hom ≫ (derivedPullback S'.toSpecΓ).map
            (schemeDerivedBaseChangeMap f0 f0' g0 g0' sq0.w K0 ≫
              (schemeDerivedDirectImage f0').map φ0) ≫ eR.inv := by
  dsimp
  let K0 := affineSpectrumDerivedObject X K
  let K0' := affineSpectrumDerivedObject X' K'
  let φ0 := affineSpectrumDerivedMorphism g' K K' φ
  have hK0 : schemeDerivedQCohProperty (Spec Γ(X, ⊤)) K0 :=
    (derivedPullback_tensor_preserve_QCoh X.isoSpec.inv).1 K hK
  have hK0' : schemeDerivedQCohProperty (Spec Γ(X', ⊤)) K0' :=
    (derivedPullback_tensor_preserve_QCoh X'.isoSpec.inv).1 K' hK'
  have hst := affineSpectrumCoordinates_stalkCondition f f' g g' sq sq0 K K' φ
  obtain ⟨eL, eR, heq⟩ :=
    affineSpectrumCoordinates_comparison f f' g g' sq sq0 K K' φ
  exact ⟨K0, K0', φ0, hK0, hK0', hst, eL, eR, heq⟩

end AlgebraicGeometry
