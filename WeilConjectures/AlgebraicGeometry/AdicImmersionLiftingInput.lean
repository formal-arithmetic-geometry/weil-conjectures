/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.AlgebraicGeometry.AdicImmersionCompletedTransport
import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueLisse
import WeilConjectures.AlgebraicGeometry.ConstantFieldResidueTensorBounds

/-! # Immersion transport of lisse residue lifting inputs

Source: Bhatt--Scholze, Proposition 6.6.11, forward implication;
Lemma 6.5.8 and Remark 6.5.10. Stacks Project, Tags 03A0, 03CY, 099L and 099R.
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

/-- The standard derived category on the original slice, with the actual inverse-image ring.
This abbreviates the codomain of `sfbLocalRestriction`; it changes no coefficient ring
(Stacks, Tag 00XZ). -/
abbrev sfbAdicImmersionSliceCategory {X S : Scheme.{u}} (i : S ⟶ X)
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (U : S.ProEt) :=
  let R := (adicLisseForget S).obj
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj (adicLisseCompletedRing X I))
  @DerivedCategory (SheafOfModules.{u + 1} (R.over U)) _ _ (HasDerivedCategory.standard _)

/-- A lisse restriction of the residue supplies the input to the existing perfect-lifting
lemma, together with its slice comparisons. This statement constructs no perfect complex
and no covering sieve. Its output remains an arbitrary complete complex with lisse residue.

Source: Bhatt--Scholze, Proposition 6.6.11, forward implication; Lemma 6.5.8 and
Remark 6.5.10; Stacks Tags 03A0, 03CY, 099L and 099R. -/
theorem sfbAdicImmersion_liftingInput
    (X S : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (i : S ⟶ X) [IsImmersion i]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal) [IsAdicComplete I A]
    (K : _)
    (hcomplete : IsSfbAdicComplete X I K)
    (C : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ)
    (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q))
    (hlisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((Etale.upperStar.{u + 2, u} (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) i).obj (C.homology q)))
    (hres : Nonempty (DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅
      DerivedCategory.Q.obj
        (((ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex (.up ℤ)).obj C))) :
    ∃ (M : ConstantCompletion.D
        (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} S) A I))
      (C' : ConstantCompletion.D
        (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0)),
      ConstantCompletion.IsComplete
        (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, 0} S) A I 0) M ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero
        ((adicResidueCohomology.{u + 1}
          (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0)
          q).obj C')) ∧
      (∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
        (smallModelComparisonEtaleTopology.{u, 0} S) (A ⧸ I ^ (0 + 1))
        ((adicResidueCohomology.{u + 1}
          (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0)
          q).obj C')) ∧
      (∀ P : ConstantCompletion.Cx
          (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0),
        CochainComplex.IsKFlatIndependentCoefficients
          (J := smallModelComparisonEtaleTopology.{u, 0} S)
          (R := ConstantCompletion.finite
            (smallModelComparisonEtaleTopology.{u, 0} S) A I 0) P →
        Nonempty ((ConstantCompletion.Q
          (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0)).obj
            P ≅ C') →
        ∀ (N : ConstantCompletion.Mod
            (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0))
          (q : ℤ), q < a ∨ b < q →
          IsZero (adicResidueTensorCohomology.{u + 1}
            (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0)
            P N q)) ∧
      Nonempty ((ConstantCompletion.extend
        (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, 0} S) A I 0)).obj
          M ≅ (adicResidueComparison.{u, 0} S (A ⧸ I ^ (0 + 1))).obj C') ∧
      ∀ U : S.ProEt, ∃ eU :
          ConstantCompletion.D
            ((ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} S) A I).over
              ((AsSmall.up : S.ProEt ⥤ coefficientProEtaleSiteModel.{u, 0} S).obj U)) ≌
            sfbAdicImmersionSliceCategory i I U,
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
  have _hab := hab
  obtain ⟨M, hM, hresM, hslices⟩ :=
    sfbAdicImmersion_completedTransport X S i A I K hcomplete C hres
  have hb := sfbImmersionResidue_bounded i I C a b hbounded
  refine ⟨M, sfbImmersionResidue i I C, hM, hb,
    sfbImmersionResidue_lisse i I C hlisse, ?_, hresM, hslices⟩
  intro P _ e N q hq
  let : (I ^ (0 + 1)).IsMaximal := by simpa using hI
  let : Field (A ⧸ I ^ (0 + 1)) := Ideal.Quotient.field _
  exact constantFieldResidueTensor_bounds
    (smallModelComparisonEtaleTopology.{u, 0} S) (A ⧸ I ^ (0 + 1))
    (sfbImmersionResidue i I C) a b hb P e N q hq

end AlgebraicGeometry.Scheme
