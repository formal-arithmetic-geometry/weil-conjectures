module

public import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import Sheaf.AlgebraicGeometry.ConstructibleTorsionModulesAgree
import Sheaf.AlgebraicGeometry.CurveCoefficientPair
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.CurveCoefficientPair
/-- Constructibility of the quotient in the six step dévissage argument.
The proof is the finite torsion bound, cyclic module bridge, cokernel Serre
property, and transport across the cokernel isomorphism described in the parent
blueprint node.
(blueprint: lem-weil-pbc-curve-constructible-quot-part) -/
theorem constructible_quot_part {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k)
    (F₁ F₂ : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h₁ : P.C.IsTorsionAbelianSheaf F₁) (h₂ : P.C.IsTorsionAbelianSheaf F₂)
    (α : F₁ ⟶ P.F) (β : P.F ⟶ F₂) (w : α ≫ β = 0)
    (hS : (ShortComplex.mk α β w).ShortExact) (hF : P.IsConstructible) :
    AlgebraicGeometry.CurveCoefficientPair.IsConstructible
      { P with F := F₂, isTorsion := h₂ } := by sorry
end AlgebraicGeometry.CurveCoefficientPair
