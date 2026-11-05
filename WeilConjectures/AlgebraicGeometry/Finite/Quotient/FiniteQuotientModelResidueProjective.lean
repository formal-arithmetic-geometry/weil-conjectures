/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive

import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientModelResidueComparison
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantSliceIsoReflects
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The algebraic residue of a finite-quotient constant model

Source: Stacks Project, sites-cohomology.tex, lemma-bounded (094I)
(blueprint: lem-weil-pbc-finite-quotient-model-residue-projective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem residueOverMap_exact (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) {U V : X.ProEt} (f : U ⟶ V) :
    (SheafOfModules.overMap.{t + 1} R f).Additive ∧
      PreservesFiniteLimits (SheafOfModules.overMap.{t + 1} R f) ∧
      PreservesFiniteColimits (SheafOfModules.overMap.{t + 1} R f) := by
  let F := SheafOfModules.overMap.{t + 1} R f
  let H := (ProEt.topology X).overMapPullback AddCommGrpCat.{t + 1} f
  have hAdd : F.Additive := ⟨fun {_ _} a b ↦ by ext V x; rfl⟩
  let e : F ⋙ SheafOfModules.toSheaf.{t + 1} (R.over U) ≅
      SheafOfModules.toSheaf.{t + 1} (R.over V) ⋙ H := Iso.refl _
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesColimitsOfSize.{t + 1, t + 1} H :=
    ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{t + 1}
      ((ProEt.topology X).over U) ((ProEt.topology X).over V)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits H :=
    PreservesColimitsOfSize.preservesFiniteColimits H
  have h (S : ShortComplex (SheafOfModules.{t + 1} (R.over V))) (hS : S.ShortExact) :
      (S.map F).ShortExact := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (SheafOfModules.toSheaf.{t + 1} (R.over U))
    exact ShortComplex.shortExact_of_iso (S.mapNatIso e.symm)
      ((hS.map_of_exact (SheafOfModules.toSheaf.{t + 1} (R.over V))).map_of_exact H)
  exact ⟨hAdd, (Functor.exact_tfae F).out 1 4 |>.mp h⟩

/-- The exact derived restriction agrees with the chosen representative formula.
Source: Stacks Tags 03DJ and 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
private def residueRestrictionComparison (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    (M : DerivedCategory (SheafOfModules.{t + 1} R)) :
    (ringedDerivedRestrictionGeneral R U).obj M ≅
      ringedSiteDerivedRestrictionOfUniverses R U M := by
  let F := SheafOfModules.overFunctor.{t + 1} R U
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)

/-- A local isomorphism persists on every smaller chart.
Source: Stacks Tag 03DJ
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
private theorem residueRestrictIso_further (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) {U V : X.ProEt} (f : U ⟶ V)
    (M N : DerivedCategory (SheafOfModules.{t + 1} R))
    (e : ringedSiteDerivedRestrictionOfUniverses R V M ≅
      ringedSiteDerivedRestrictionOfUniverses R V N) :
    Nonempty (ringedSiteDerivedRestrictionOfUniverses R U M ≅
      ringedSiteDerivedRestrictionOfUniverses R U N) := by
  let F := SheafOfModules.overMap.{t + 1} R f
  let FV := SheafOfModules.overFunctor.{t + 1} R V
  let FU := SheafOfModules.overFunctor.{t + 1} R U
  have := (residueOverMap_exact X R f).1
  have := (residueOverMap_exact X R f).2.1
  have := (residueOverMap_exact X R f).2.2
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  have := (ringedOverFunctor_exactGeneral R V).1
  have := (ringedOverFunctor_exactGeneral R V).2.1
  have := (ringedOverFunctor_exactGeneral R V).2.2
  have c (K : DerivedCategory (SheafOfModules.{t + 1} R)) :
      F.mapDerivedCategory.obj (ringedSiteDerivedRestrictionOfUniverses R V K) ≅
        ringedSiteDerivedRestrictionOfUniverses R U K :=
    F.mapDerivedCategory.mapIso (residueRestrictionComparison X R V K).symm ≪≫
      (Functor.mapDerivedCategoryCompIso FV F).symm.app K ≪≫
      (Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap R f)).app K ≪≫
      residueRestrictionComparison X R U K
  exact ⟨(c M).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫ c N⟩

end AlgebraicGeometry.Scheme
