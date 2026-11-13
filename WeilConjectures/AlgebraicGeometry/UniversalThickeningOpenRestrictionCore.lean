/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenPieces

/-!
# Open restriction of universal first order thickenings

A universal first order thickening restricts to a universal first order thickening over opens
of the source and target.

## References

* [Stacks Project, Tag 04FA](https://stacks.math.columbia.edu/tag/04FA)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The open restriction data for a universal first order thickening exists: for opens
`V ⊆ h⁻¹ U`, there is an open `V'` of `Z'` with `i⁻¹ V' = V` such that the restricted maps form a
universal first order thickening of `V ⟶ U`. -/
theorem universalFirstOrderThickening_open_restriction_core
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : IsUniversalFirstOrderThickening h i h')
    (V : Z.Opens) (U : X.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    ∃ (hV : V.toScheme ⟶ U.toScheme),
      V.ι ≫ h = hV ≫ U.ι ∧ ∃ (V' : Z'.Opens) (iV : V.toScheme ⟶ V'.toScheme)
          (hV' : V'.toScheme ⟶ U.toScheme),
          i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
          iV ≫ V'.ι = V.ι ≫ i ∧ hV' ≫ U.ι = V'.ι ≫ h' ∧
          iV ≫ hV' = hV ∧ IsUniversalFirstOrderThickening hV iV hV' := by
  obtain ⟨V', hiV', hV'U, iV, hV, hV', hiV, hhV, hhV', HV⟩ :=
    (universalFirstOrderThickening_open_pieces h).2.1 i h' H V U hVU
  exact ⟨hV, hhV.symm, V', iV, hV', hiV', hV'U, hiV, hhV', HV.2.1, HV⟩

end AlgebraicGeometry
