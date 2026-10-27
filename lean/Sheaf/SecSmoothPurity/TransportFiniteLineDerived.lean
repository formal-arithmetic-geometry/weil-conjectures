module
public import Sheaf.SecSmoothPurity.TransportFiniteLines
public import Sheaf.SecSmoothPurity.TransportUnits
public import Sheaf.AlgebraicGeometry.ComparisonConstantGenerator

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-finite-derived-line-coordinates). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]
variable (A : CommRingCat.{0}) [fin : Finite A] (n : ℕ)
  (hA : (ell ^ (n + 1) : A) = 0) (X : Scheme.{u})
  (hX : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(X, ⊤)))
  (p : FiniteLineCoordinates ell A fin n hA X hX)
local instance : TopologicalSpace A := ⊥
local instance : DiscreteTopology A := discreteTopology_bot A

/-- The degree-zero unit comparison, including the fixed site comparison.
Source: constant sections normalization
(blueprint: def-pur-transport-finite-derived-line-coordinates). -/
def finiteDerivedUnit :
    (finiteEncodingDerived A X).inverse.obj
      (unit ell (.finite A fin n hA) X) ≅
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit (ULift.{u + 1} A) X) :=
  ((finiteEncoding A X).inverse.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso p.unit ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((ProEtale.comparisonUpperStarConstantSheafIso (ULift.{u + 1} A) X).app
        (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))).symm ≪≫
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategorySingleFunctor 0).symm.app _

/-- The shifted finite Tate comparison induced by the normalized ordinary map.
Source: root and site comparison (blueprint: def-pur-transport-finite-derived-line-coordinates). -/
def finiteDerivedLine :
    (finiteEncodingDerived A X).inverse.obj
      ((Coefficient.finite A fin n hA).derivedLine ell X 1) ≅
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.obj
        ((Etale.ordinaryFiniteLine (ULift.{u + 1} A) (ell ^ (n + 1))
          (finiteLiftAnnihilator ell A n hA) X) ⟦(2 : ℤ)⟧) := by
  let F := (finiteEncoding A X).inverse
  let G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  let e := F.mapIso ((λ_ ((Coefficient.finite A fin n hA).firstLine ell X)) ≪≫ p.line) ≪≫
    (finiteEncoding A X).unitIso.symm.app _
  exact (Functor.commShiftIso F.mapDerivedCategory (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
        (G.mapDerivedCategorySingleFunctor 0).symm.app _) ≪≫
    ((Functor.commShiftIso G.mapDerivedCategory (2 : ℤ)).app _).symm

end AlgebraicGeometry.ProEtale.PurityTransport
