module

public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The open restriction data for a universal first order thickening exists.
Source: Stacks Project, More on Morphisms, Lemma 04FA and the general remarks in
Lemma 04F3 (blueprint: lem-weil-pbc-universal-thickening-open-restriction-core).
The proof restricts the closed immersion to the open determined by the image of
`V`, factors the structure maps through `U`, and applies the universal lifting
property; these constructions give the displayed equalities and universality. -/
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
  sorry

end AlgebraicGeometry
