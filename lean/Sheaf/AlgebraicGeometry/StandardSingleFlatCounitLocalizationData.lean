module

public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The bounded termwise-flat stalk complex needed as the first stage of the
localization construction.  This is the stalkwise bounded/flat part of the
local sheaf presentation argument; the remaining derived counit data are proved
separately. Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
(blueprint: lem-pc-standard-single-flat-counit-localization-data). -/
theorem standardSingleFlatCounit_localization_data
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P.X i)) := by sorry

end AlgebraicGeometry
