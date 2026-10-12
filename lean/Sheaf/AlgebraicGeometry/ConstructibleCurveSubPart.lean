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
/-- Constructibility of the subobject in the six step dévissage argument.
The proof is the finite torsion bound, cyclic module bridge, and the Noetherian
constructible subobject theorem described in the parent blueprint node.
(blueprint: lem-weil-pbc-curve-constructible-sub-part) -/
theorem constructible_sub_part {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k)
    (F₁ F₂ : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h₁ : P.C.IsTorsionAbelianSheaf F₁) (h₂ : P.C.IsTorsionAbelianSheaf F₂)
    (α : F₁ ⟶ P.F) (β : P.F ⟶ F₂) (w : α ≫ β = 0)
    (hS : (ShortComplex.mk α β w).ShortExact) (hF : P.IsConstructible) :
    AlgebraicGeometry.CurveCoefficientPair.IsConstructible
      { P with F := F₁, isTorsion := h₁ } := by sorry
end AlgebraicGeometry.CurveCoefficientPair
