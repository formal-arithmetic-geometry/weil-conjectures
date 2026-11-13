/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Restriction of the bare base-change arrow

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The restriction calculation for the bare base-change arrow (identity
coefficient). The direct-image comparison is natural on all target coefficients;
no stalk condition, target coefficient K', or arbitrary coefficient map is assumed. -/
theorem singleComplexOpen_baseChange_identity
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV')) :
    let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
    let R := (schemeOpenRestriction S' V').mapDerivedCategory
    let R' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory
    let δ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    ∃ (a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj K)) ≅
          (derivedPullback (g.resLE V V' hV')).obj
            ((schemeDerivedDirectImage (f ∣_ V)).obj K₀))
      (b : schemeDerivedDirectImage f' ⋙ R ≅ R' ⋙ schemeDerivedDirectImage (f' ∣_ V')),
      R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K) =
        a.hom ≫ schemeDerivedBaseChangeMap
          (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀.w K₀ ≫
          (schemeDerivedDirectImage (f' ∣_ V')).map δ ≫
          b.inv.app ((derivedPullback g').obj K) := by
  refine ⟨singleComplexOpenBaseChangeSourceIso f g K V V' hV',
    singleComplexOpenDirectImageIso f' V', ?_⟩
  exact singleComplexOpen_baseChange_calculation f f' g g' sq K V V' hV' j hj sq₀

end AlgebraicGeometry
