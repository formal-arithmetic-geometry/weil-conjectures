/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCoordinateStalkEquivalence

/-! # Transporting K-flat coordinates to opens

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Transport one K-flat coordinate system to compatible target opens.
This concerns the comparison in these coordinates, not the universally quantified
stalk condition and not the base-change arrow. -/
theorem singleComplexOpen_coordinates_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (c : SingleComplexBaseChange.Coordinates g' K K' φ)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV')) :
    let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
    let K₀' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.obj K'
    let φ₀ := singleComplexRestrictedCoefficient g' K K' φ
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    ∃ d : SingleComplexBaseChange.Coordinates j K₀ K₀' φ₀,
      ∀ (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ),
        IsIso (SingleComplexBaseChange.stalkComparison
          (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ d z i) ↔
        IsIso (SingleComplexBaseChange.stalkComparison f f' g g' sq c z.val i) := by
  classical
  dsimp only
  let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
  let K₀' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.obj K'
  let φ₀ := singleComplexRestrictedCoefficient g' K K' φ
    (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
  obtain ⟨d⟩ := SingleComplexBaseChange.nonempty_coordinates j K₀ K₀' φ₀
  refine ⟨d, ?_⟩
  intro z i
  obtain ⟨e⟩ := nonempty_singleComplexOpen_stalk_arrow_iso
    f f' g g' sq K K' φ c V V' hV' j hj sq₀ d z i
  let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z))
    AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
  constructor
  · intro h
    have : IsIso (F₀.map (SingleComplexBaseChange.stalkComparison
        (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ d z i)) := inferInstance
    have := (Arrow.isIso_iff_isIso_of_isIso e.hom).mp this
    exact isIso_of_reflects_iso _ F
  · intro h
    have : IsIso (F.map
        (SingleComplexBaseChange.stalkComparison f f' g g' sq c z.val i)) := inferInstance
    have := (Arrow.isIso_iff_isIso_of_isIso e.hom).mpr this
    exact isIso_of_reflects_iso _ F₀

end AlgebraicGeometry
