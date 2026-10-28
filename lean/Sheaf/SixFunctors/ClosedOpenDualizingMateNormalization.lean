module
public import Sheaf.SixFunctors.ClosedOpenDualizingMate
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale
theorem closedOpen_dualizingMate_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X V P S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian V] [IsNoetherian P] [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : V ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p]
    (h : j ≫ f = i ≫ p)
    (hω : DerivedCategory.isBoundedConstructible A X
        (dualizingComplex (ModuleCat.{u + 1} A) f) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b
        (dualizingComplex (ModuleCat.{u + 1} A) f)) :
    ∃ (eA : (derivedRestriction (A := A) j).obj
          (dualizingComplex (ModuleCat.{u + 1} A) f) ≅
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) i).obj
          (dualizingComplex (ModuleCat.{u + 1} A) p))
      (eB : (derivedRestriction (A := B) j).obj
          (dualizingComplex (ModuleCat.{u + 1} B) f) ≅
        (rightDerivedUpperShriek (ModuleCat.{u + 1} B) i).obj
          (dualizingComplex (ModuleCat.{u + 1} B) p)),
      (openScalarRestriction φ j).hom.app (dualizingComplex (ModuleCat.{u + 1} A) f) ≫
          (derivedRestriction (A := B) j).map
            (ExceptionalCoefficients.dualizingScalarMap φ f) ≫ eB.hom =
        (scalarExtension φ V).map eA.hom ≫
          closedDualizingCoefficientMate φ i (dualizingComplex (ModuleCat.{u + 1} A) p) ≫
          (rightDerivedUpperShriek (ModuleCat.{u + 1} B) i).map
            (ExceptionalCoefficients.dualizingScalarMap φ p) := by sorry
end AlgebraicGeometry.Etale
