module

public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison

@[expose] public section

universe u' u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section

variable {X : Scheme.{u}}

lemma isIso_derivedAdjunction_comparisonAdjunction_unit_app
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hM : DerivedCategory.TStructure.t.plus M) :
    IsIso ((comparisonAdjunction A X).derivedAdjunction.unit.app M) := by
  have h := isIso_derivedComparisonAdjunction_unit_app A X M hM
  simp only [derivedComparisonAdjunction, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app] at h
  exact IsIso.of_isIso_comp_right _ ((R(ν_*(X)[A])).map
    ((ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory.hom.app M))

end

end AlgebraicGeometry.ProEtale
