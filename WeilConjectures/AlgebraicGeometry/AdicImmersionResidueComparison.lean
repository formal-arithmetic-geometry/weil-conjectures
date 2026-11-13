/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueComparisonCore
import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueComparisonEtale
import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueComparisonFixed

/-! # Residue comparisons for the specified completed immersion pullback

Source: Stacks Tags 03A0, 03CY, 06YY, 099L and 099R.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Pure inverse image of a fixed-scalar residue, followed by the actual small-site
and constant-ring equivalences: the public name of
`SfbResidueComparisonCore.sfbFixedResiduePull`, whose exactness instances it inherits.
Source: Stacks Tags 03A0 and 03CY. -/
abbrev sfbFixedResiduePull {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k) ⥤
      ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S) k) :=
  SfbResidueComparisonCore.sfbFixedResiduePull i k

private local instance modelSheafify (S : Scheme.{u}) :
    HasSheafify (proEtaleModelTopology S) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance modelLocallyBijective (S : Scheme.{u}) :
    (proEtaleModelTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}

attribute [local instance 50000] modelSheafify modelLocallyBijective fixedSheafify

private local instance standardDerived {D : Type (u + 1)} [SmallCategory D]
    {J : GrothendieckTopology D} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

private local instance fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

private noncomputable local instance modelAbelian (S : Scheme.{u})
    (R : Sheaf (proEtaleModelTopology S) CommRingCat.{u + 1}) :
    Abelian (ConstantCompletion.Mod R) :=
  SheafOfModules.instAbelian.{u + 1, u + 1, u + 1, u + 1} _

private noncomputable local instance fixedAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian (proEtaleRingModules X R) :=
  SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _

attribute [local instance 40000] modelAbelian fixedAbelian standardDerived
  fixedLocallyBijective
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

attribute [-instance] coefficientModelAdditiveSheafify coefficientEtaleModelAdditiveSheafify
  ConstantScalarRestriction.ringAbelian ConstantScalarRestriction.fixedAbelian
  ConstantScalarRestriction.ringGrothendieck ConstantScalarRestriction.fixedGrothendieck
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
/-- The residue-projection and etale-comparison squares for a fixed completed model.
These are assertions about the functors themselves: they require neither completeness
nor a chosen residue isomorphism.

Source: Stacks Tags 03A0, 03CY, 06YY, 099L and 099R; Bhatt--Scholze, Lemma 6.5.8. -/
theorem sfbImmersion_residueComparisons
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    letI := HasDerivedCategory.standard
      (ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S)
        (A ⧸ I ^ (0 + 1))))
    (∀ K : @DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)) _ _
        (proEtaleRingModules_hasDerivedCategory X (adicLisseCompletedRing X I)),
      Nonempty ((ConstantCompletion.extend
        (ConstantCompletion.projection (proEtaleModelTopology S) A I 0)).obj
          (sfbImmersionCompletedModel i I K) ≅
        (Functor.mapDerivedCategory.{u + 1, u + 2}
          (sfbFixedResiduePull i (A ⧸ I ^ (0 + 1)))).obj
          (DerivedCategory.Q.obj (sfbResidueComplex X I K)))) ∧
    (∀ C : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ,
      Nonempty ((Functor.mapDerivedCategory.{u + 1, u + 2}
          (sfbFixedResiduePull i (A ⧸ I ^ (0 + 1)))).obj
          (DerivedCategory.Q.obj
            (((ProEtale.comparisonUpperStar.{u + 2, u}
              (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex
                (.up ℤ)).obj C)) ≅
        (adicResidueComparison.{u, 0} S (A ⧸ I ^ (0 + 1))).obj
          (sfbImmersionResidue i I C))) := by
  dsimp
  exact ⟨sfbImmersion_residueComparison_fixed i I,
    sfbImmersion_residueComparison_etale i I⟩

end AlgebraicGeometry.Scheme
