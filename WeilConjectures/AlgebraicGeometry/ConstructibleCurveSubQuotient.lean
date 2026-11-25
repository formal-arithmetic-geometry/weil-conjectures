/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleCurveSubPart
import WeilConjectures.AlgebraicGeometry.ConstructibleCurveQuotPart
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionModulesAgree
import WeilConjectures.AlgebraicGeometry.CurveCoefficientPair
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Subobjects and quotients of constructible torsion sheaves on curves

## References

* Stacks Project, Tag 09BH (2), Tag 03RW and Tag 095E
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.CurveCoefficientPair

/-- In a short exact sequence of torsion abelian sheaves on a curve, constructibility of
its middle term implies constructibility of both outer terms.
(Stacks, Tag 09BH (2), Tag 03RW and Tag 095E) -/
theorem constructible_sub_quotient {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k)
    (F₁ F₂ : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h₁ : P.C.IsTorsionAbelianSheaf F₁) (h₂ : P.C.IsTorsionAbelianSheaf F₂)
    (α : F₁ ⟶ P.F) (β : P.F ⟶ F₂) (w : α ≫ β = 0)
    (hS : (ShortComplex.mk α β w).ShortExact) (hF : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F))) :
    ((fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F))) { P with F := F₁, isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp h₁) }) ∧
      ((fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
        { P with F := F₂, isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp h₂) }) := by
  exact ⟨constructible_sub_part P F₁ F₂ h₁ h₂ α β w hS hF,
    constructible_quot_part P F₁ F₂ h₁ h₂ α β w hS hF⟩

end AlgebraicGeometry.CurveCoefficientPair
