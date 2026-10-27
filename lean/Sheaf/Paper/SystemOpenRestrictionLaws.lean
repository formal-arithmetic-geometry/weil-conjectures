module
public import Sheaf.Paper.SystemCompactSupportRestrictionData
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.longLine false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
/-- Coherence laws follow from summandwise identity, sheafification uniqueness and exact localization. (blueprint: lem-sp-system-open-restriction-laws) -/
theorem systemOpenRestrictionLaws (l : ℕ) [Fact l.Prime] {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (c : RestrictionIdentifications.{u} l)
    (g : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l) (a : B.rings ⟶ C.rings), GeometricSquare a j)
    (o : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l) (a : B.rings ⟶ C.rings), OpenComparison (g B C a)) :
    (∀ (B C D : Etale.SystemProjection.Coefficients.{u} l) (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings) (L : VaryingRing.Derived (levels D) (steps D) X), (VaryingRing.J (levels B) (steps B) j).map ((c.rho X a b).hom.app L) ≫ (o B D (a ≫ b)).derived.hom.app L = (o B C a).derived.hom.app ((derivedRestriction X b).obj L) ≫ (derivedRestriction Z a).map ((o C D b).derived.hom.app L) ≫ (c.rho Z a b).hom.app ((VaryingRing.J (levels D) (steps D) j).obj L)) ∧
    (∀ (B : Etale.SystemProjection.Coefficients.{u} l) (L : VaryingRing.Derived (levels B) (steps B) X), (o B B (𝟙 B.rings)).derived.hom.app L ≫ (c.derivedUnit Z B).hom.app ((VaryingRing.J (levels B) (steps B) j).obj L) = (VaryingRing.J (levels B) (steps B) j).map ((c.derivedUnit X B).hom.app L)) := by
  sorry
end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
