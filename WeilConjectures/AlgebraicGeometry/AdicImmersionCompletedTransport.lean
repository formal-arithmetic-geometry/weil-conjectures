/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueTransport
import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueComparison
import WeilConjectures.AlgebraicGeometry.AdicImmersionSliceComparison

/-! # Completed restriction and residue comparison for an immersion

## References

* Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.8 and Remark 6.5.10
* Stacks Project, Tags 03A0, 03CY, 099L and 099R
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private local instance fixedLocallyBijective (S : Scheme.{u}) :
    (ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

private noncomputable local instance fixedAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian (proEtaleRingModules X R) :=
  SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _

attribute [local instance 40000] fixedAbelian

attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

/-- Completed inverse image with its normalized residue and slice comparisons
(Bhatt--Scholze, Lemma 6.5.8 and Remark 6.5.10; Stacks, Tags 03A0, 03CY, 099L and 099R). -/
theorem sfbAdicImmersion_completedTransport
    (X S : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (i : S ⟶ X) [IsImmersion i]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    (K : _)
    (hcomplete : IsSfbAdicComplete X I K)
    (C : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ)
    (hres : Nonempty (DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅
      DerivedCategory.Q.obj
        (((ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex (.up ℤ)).obj C))) :
    ∃ (M : ConstantCompletion.D
        (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} S) A I)),
      ConstantCompletion.IsComplete
        (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, 0} S) A I 0) M ∧
      Nonempty ((ConstantCompletion.extend
        (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, 0} S) A I 0)).obj
          M ≅ (adicResidueComparison.{u, 0} S (A ⧸ I ^ (0 + 1))).obj (sfbImmersionResidue i I C)) ∧
      ∀ U : S.ProEt, ∃ eU :
          ConstantCompletion.D
            ((ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} S) A I).over
              ((AsSmall.up : S.ProEt ⥤ coefficientProEtaleSiteModel.{u, 0} S).obj U)) ≌
            (let R := (adicLisseForget S).obj
              ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj
                (adicLisseCompletedRing X I))
             @DerivedCategory (SheafOfModules.{u + 1} (R.over U)) _ _
               (HasDerivedCategory.standard _)),
        Nonempty (sfbLocalRestriction i (adicLisseCompletedRing X I) U K ≅
          eU.functor.obj ((adicResidueRestriction.{u + 1}
            (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} S) A I)
            ((AsSmall.up : S.ProEt ⥤ coefficientProEtaleSiteModel.{u, 0} S).obj U)).obj M)) ∧
        ∀ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
          Nonempty (eU.functor.obj ((adicResidueRestriction.{u + 1}
            (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} S) A I)
            ((AsSmall.up : S.ProEt ⥤ coefficientProEtaleSiteModel.{u, 0} S).obj U)).obj
              (adicResidueConstantPerfect.{u, 0} S I P)) ≅
            sfbLocalRestriction i (adicLisseCompletedRing X I) U (sfbCompletedModel X I P)) := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  have hunit := (SfbAdicRestriction.adicStratumCompletionUnit X A I r a ha).1
    S i (sfbImmersionAlgebra i)
  refine ⟨sfbImmersionCompletedModel i I K, ?_, ?_, ?_⟩
  · exact hunit.2.2.2.2 _ ((SfbCompletionNormalization.complete_iff X I K).mp hcomplete)
  · let : HasSheafify (proEtaleModelTopology S) AddCommGrpCat.{u + 1} :=
      SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u + 1, u + 1}
    let : (proEtaleModelTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u + 1, u + 1}
    let : Abelian (ConstantCompletion.Mod
        (ConstantCompletion.constant (proEtaleModelTopology S) (A ⧸ I ^ (0 + 1)))) :=
      SheafOfModules.instAbelian.{u + 1, u + 1, u + 1, u + 1} _
    let := HasDerivedCategory.standard
      (ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S)
        (A ⧸ I ^ (0 + 1))))
    obtain ⟨eK⟩ := (sfbImmersion_residueComparisons i I).1 K
    obtain ⟨eC⟩ := (sfbImmersion_residueComparisons i I).2 C
    obtain ⟨e⟩ := hres
    let F := Functor.mapDerivedCategory.{u + 1, u + 2}
      (sfbFixedResiduePull i (A ⧸ I ^ (0 + 1)))
    exact ⟨eK ≪≫ F.mapIso e ≪≫ eC⟩
  · intro U
    obtain ⟨eU, hK, hP⟩ := sfbImmersion_sliceComparisons i I U
    exact ⟨eU, hK K, hP⟩

end AlgebraicGeometry.Scheme
