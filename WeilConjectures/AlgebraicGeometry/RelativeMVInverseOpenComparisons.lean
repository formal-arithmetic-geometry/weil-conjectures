/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVExactOpenComparison
import WeilConjectures.AlgebraicGeometry.RelativeMVInverseOpenMate

/-! # Inverse-image open comparisons with units, restrictions, and base change

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Comparisons on individual inverse-image opens, compatible with their units,
restrictions along one inclusion, and the pasted base-change map. -/
theorem relativeMV_inverse_open_comparisons
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') :
    ∃ e : ∀ W : X.Opens,
      (schemeDerivedDirectImage f').obj
        ((schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).obj
          ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.obj K')) ≅
        (relativeMVLocalArrow f f' g g' hpull K K' φ W).right,
      (∀ W : X.Opens,
        (schemeDerivedDirectImage f').map
            ((mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)).unit.app K') ≫ (e W).hom =
          relativeMVUnit (pullback.fst g' W.ι) f' K') ∧
      (∀ (W U : X.Opens) (i : W ≤ U),
        (schemeDerivedDirectImage f').map
            (schemeDerivedOpenDirectImageRestriction X'
              ((TopologicalSpace.Opens.map g'.base).map (homOfLE i))
              (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
              (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)) K') ≫ (e W).hom =
          (e U).hom ≫ relativeMVRestriction (relativeMVOpenLift g' i)
            (pullback.fst g' U.ι) (pullback.fst g' W.ι)
            (pullback.lift_fst _ _ _) f' K') ∧
      (∀ W : X.Opens,
        mvBaseChangeOpenMap f f' g g' hpull.w K K' φ W ≫ (e W).hom =
          ((derivedPullback g).mapIso (relativeMVExactOpenIso f W K)).hom ≫
            (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom) := by
  refine ⟨fun W ↦ relativeMVInverseOpenIso g' f' W K', ?_, ?_, ?_⟩
  · intro W
    exact relativeMVInverseOpenIso_unit g' f' W K'
  · intro W U i
    exact relativeMVInverseOpenIso_restriction g' f' i K'
  · intro W
    exact relativeMVInverseOpenIso_mate f f' g g' hpull K K' φ W

end AlgebraicGeometry
