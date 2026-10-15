module
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.KFlatResolution
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A fixed K-flat replacement of the second coefficient in degree zero. -/
theorem exists_tensorResolutionSecondKFlat (Y : Scheme.{u}) (N : Y.Modules) :
    ∃ (F : CochainComplex Y.Modules ℤ)
      (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N),
      CochainComplex.IsKFlat (R := Y.sheaf) F ∧ QuasiIso s := by
  obtain ⟨F, s, hF, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf)
    ((CochainComplex.singleFunctor Y.Modules 0).obj N)
  exact ⟨F, s, hF, hs⟩

end AlgebraicGeometry
