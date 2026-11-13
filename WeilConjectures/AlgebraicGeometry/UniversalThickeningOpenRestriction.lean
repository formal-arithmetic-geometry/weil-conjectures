/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormallyUnramifiedConormal
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenRestrictionCore
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenRestrictionConormal

/-!
# Universal thickenings and conormal sheaves on open subschemes

## References

* [Stacks Project, Tag 04FA](https://stacks.math.columbia.edu/tag/04FA)
* [Stacks Project, Tag 02HC](https://stacks.math.columbia.edu/tag/02HC)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Universal first order thickenings, formal unramifiedness, and conormal sheaves
restrict to compatible open subschemes. -/
theorem universalFirstOrderThickening_open_restriction
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : IsUniversalFirstOrderThickening h i h')
    (hform : FormallyUnramified h)
    (V : Z.Opens) (U : X.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    ∃ (hV : V.toScheme ⟶ U.toScheme),
      V.ι ≫ h = hV ≫ U.ι ∧ FormallyUnramified hV ∧
        ∃ (V' : Z'.Opens) (iV : V.toScheme ⟶ V'.toScheme)
          (hV' : V'.toScheme ⟶ U.toScheme),
          i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
          iV ≫ V'.ι = V.ι ≫ i ∧
            hV' ≫ U.ι = V'.ι ≫ h' ∧
            iV ≫ hV' = hV ∧
            IsUniversalFirstOrderThickening hV iV hV' ∧
            ∃ (hVform : FormallyUnramified hV),
              ∃ (HV : IsUniversalFirstOrderThickening hV iV hV'),
                Nonempty
                  ((Scheme.Modules.restrictFunctor V.ι).obj
                      (@formallyUnramifiedConormal _ _ _ h hform i h' H) ≅
                    @formallyUnramifiedConormal _ _ _ hV hVform iV hV' HV) := by
  obtain ⟨hV, hVeq, V', iV, hV', hdata⟩ :=
    universalFirstOrderThickening_open_restriction_core h i h' H V U hVU
  obtain ⟨hVform, HV, hiso⟩ :=
    universalFirstOrderThickening_open_restriction_conormal
      h i h' H hform hdata
  exact ⟨hV, hVeq, hVform, V', iV, hV', hdata.1, hdata.2.1, hdata.2.2.1,
    hdata.2.2.2.1, hdata.2.2.2.2.1, hdata.2.2.2.2.2, ⟨hVform, HV, hiso⟩⟩

end AlgebraicGeometry
