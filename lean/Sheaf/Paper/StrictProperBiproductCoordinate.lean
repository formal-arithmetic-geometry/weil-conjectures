module

public import Sheaf.Paper.ScalarReductionTowerBalancing
public import Sheaf.Paper.StrictScalarMateEvaluationData
public import Sheaf.Paper.FiniteScalarCoordinateData

/-! Coordinate form of the strict finite proper biproduct comparison.

Source: Stacks 0B56, 0940, 0944.
(blueprint: lem-pur-compact-support-strict-scalar-mate-strict-coordinate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

universe u

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Each finite product projection of the strict proper scalar mate is the
corresponding projection of the normalized strict-tower coordinates.  The full
strict proper biproduct identity follows by `Pi.hom_ext`; this is its individual
finite-free column calculation in the whole diagram category.
Source: Stacks 0B56, equation-projection-formula-map, and 0940, section-derived-limits.
(blueprint: lem-pur-compact-support-strict-scalar-mate-strict-coordinate). -/
theorem strictProper_biproduct_coordinate {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) ≅
      (pbcRestrict (constantMap l E F i W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj ((constants l F).ring W))))
    (bZ : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget Z).obj ((constants l E).ring Z))) ≅
      (pbcRestrict (constantMap l E F i Z)).obj
        (SheafOfModules.unit ((adicLisseForget Z).obj ((constants l F).ring Z))))
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z)
    (j : Fin d) :
    (U l E F i W).map ((proper l E F i g).app N) ≫
        (properRestriction l E F i g).hom.app ((T l E F i Z).obj N) ≫
        (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
          ((derivedTowerCoordinates Z (constantMap l E F i Z) d bZ).hom.app N) ≫
        piComparison (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
          (fun _ : Fin d ↦ N) ≫
        Pi.π (fun _ : Fin d ↦
          (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) j =
      (derivedTowerCoordinates W (constantMap l E F i W) d bW).hom.app
        ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) ≫
        Pi.π (fun _ : Fin d ↦
          (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) j := by
  sorry

end WeilConjectures.PurStrictScalar
