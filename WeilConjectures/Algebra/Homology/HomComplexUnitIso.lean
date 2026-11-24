/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality

/-!
# Hom complexes from the structure sheaf

## References

* Stacks Project, Sections 0A8X and 08J7
-/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace CategoryTheory

/-- Hom from the unit concentrated in degree zero is naturally the identity on complexes. -/
theorem homComplex_unit_iso
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) :
    Nonempty ((homComplexFunctor (R := R)).obj
      (op ((CochainComplex.singleFunctor
        (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) 0).obj
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))) ≅
        𝟭 _) := by
  classical
  let F := homComplexUnitFunctor J R
  have hIso (M) (n) := homComplex_unit_evaluation_isIso J R M n
  let e := fun M => HomologicalComplex.Hom.isoOfComponents
    (fun n => asIso (homComplexUnitEvaluation J R M n))
    (fun n m h => homComplex_unit_evaluation_comm J R M n m h)
  refine ⟨NatIso.ofComponents e ?_⟩
  intro M N f
  apply HomologicalComplex.hom_ext
  intro n
  exact homComplex_unit_evaluation_naturality J R f n

end CategoryTheory
