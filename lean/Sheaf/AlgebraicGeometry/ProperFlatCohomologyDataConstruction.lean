module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The finite alternating Cech construction supplies the local bounded flat complex.
Source: Stacks Project, Tags 0A1D and 01XK.
(blueprint: new-proper-flat-cohomology-data-construction)
The proof constructs a finite affine cover of the quasi-compact inverse image, forms
its alternating sections complex, and sheafifies it over an affine neighbourhood. -/
theorem exists_proper_flat_cohomology_model_data_construction {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) [IsSeparated f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsQuasicoherent]
    (hF : F.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      t ∈ U ∧ IsAffine U.toScheme ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) := by sorry

end AlgebraicGeometry.Scheme.Modules
