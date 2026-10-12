module

public import Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal
import Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestrictionCore
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The conormal comparison for the open restriction data.
Source: Stacks Project, More on Morphisms, Lemma 04FA and Definition 01R2
(blueprint: lem-weil-pbc-universal-thickening-open-restriction-conormal).
The restriction of the kernel ideal along an open immersion identifies with the
kernel ideal of the restricted thickening; tensor pullback composition and the
open-immersion pullback/restriction comparison then give the displayed module
isomorphism. Independence of the chosen universal thickening supplies the
formally unramified witness and the displayed `HV`. -/
theorem universalFirstOrderThickening_open_restriction_conormal
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : IsUniversalFirstOrderThickening h i h')
    (hform : FormallyUnramified h)
    {V : Z.Opens} {U : X.Opens}
    {hV : V.toScheme ⟶ U.toScheme} {V' : Z'.Opens}
    {iV : V.toScheme ⟶ V'.toScheme} {hV' : V'.toScheme ⟶ U.toScheme}
    (hdata : i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
      iV ≫ V'.ι = V.ι ≫ i ∧ hV' ≫ U.ι = V'.ι ≫ h' ∧
      iV ≫ hV' = hV ∧ IsUniversalFirstOrderThickening hV iV hV') :
    ∃ (hVform : FormallyUnramified hV),
      ∃ (HV : IsUniversalFirstOrderThickening hV iV hV'),
        Nonempty
          ((Scheme.Modules.restrictFunctor V.ι).obj
              (@formallyUnramifiedConormal _ _ _ h hform i h' H) ≅
            @formallyUnramifiedConormal _ _ _ hV hVform iV hV' HV) := by
  sorry

end AlgebraicGeometry
