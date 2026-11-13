/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.FixedScalarComplexModel
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import all WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import WeilConjectures.AlgebraicGeometry.IntegralResidueModelComparison
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory

/-! # First residue under the normalized integral coefficient comparison

## References

* Stacks, Tags 099C, 099M and 09C1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  Mod.extendScalars Mod.comap Functor.mapDerivedCategory Functor.leftDerivedFunctor

namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

attribute [local instance] CategoryTheory.moduleMonoidal CategoryTheory.moduleSymmetric
  CategoryTheory.moduleClosed CategoryTheory.modulePreadditive CategoryTheory.moduleGrothendieck
  CategoryTheory.flatResolution CategoryTheory.standardDerived

private local instance transportSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private local instance transportAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private local instance transportAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify in
/-- The two integral presentations have the same constructible finite-Tor first residue
in constant-ring coordinates. This is solely coefficient transport; no etale descent,
completeness or etale-origin witness is asserted. -/
theorem integral_residue_coefficient_transport (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (hk : IsNoetherianRing
      (IntegralConstantCompletion.integers l E ⧸ IntegralConstantCompletion.ideal l E ^ (0 + 1)))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :
    letI := hk
    let k := IntegralConstantCompletion.integers l E ⧸
      IntegralConstantCompletion.ideal l E ^ (0 + 1)
    let M := Scheme.fixedScalarDerivedModel X k
      (Scheme.sfbResidueComplex X (IntegralConstantCompletion.ideal l E)
        ((IntegralConstantModel.derived l E X).functor.obj K))
    residueCondition l E X ((restriction l E X).obj K) ↔
      (∀ q : ℤ, Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u} X k
        ((coefficientModelCohomology _ q).obj M)) ∧
      Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u} X k M := by
  let := hk
  let k := IntegralConstantCompletion.integers l E ⧸
    IntegralConstantCompletion.ideal l E ^ (0 + 1)
  let M := Scheme.fixedScalarDerivedModel X k
    (Scheme.sfbResidueComplex X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K))
  let A := Padic.coefficientExtensionRing l E 1
  obtain ⟨c, hc, ⟨hMon⟩, hcons⟩ :=
    discrete_coefficient_model X A k (integralResidueScalarEquiv l E)
  let F := discreteCoefficientModel X A k c
  let : F.Monoidal := hMon
  let : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  let RI := condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X
  let := (residueTensorColimits X RI).1
  let := (residueTensorColimits X RI).2
  let := residueFlatResolution X RI
  let := residueExtensionKFlat X _ _ (residueMap l E X)
  let L : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj A) X)) :=
    (Mod.extendScalars (residueMap l E X)).leftDerivedFunctor.obj
    ((restriction l E X).obj K)
  obtain ⟨i⟩ := integral_residue_model_comparison l E X c hc K
  have hH : (∀ q : ℤ, IsConstantModelConstructible (discreteObj A) X
      ((DerivedCategory.homologyFunctor _ q).obj L)) ↔
      ∀ q : ℤ, Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u} X k
        ((coefficientModelCohomology _ q).obj M) := by
    apply forall_congr'
    intro q
    let j := (F.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
      (coefficientModelCohomology _ q).mapIso i
    refine (hcons ((DerivedCategory.homologyFunctor _ q).obj L)).trans ?_
    constructor
    · intro h
      exact coefficientProEtale_constructible_of_iso X k j h
    · intro h
      exact coefficientProEtale_constructible_of_iso X k j.symm h
  let RA := condensedRingObj (discreteObj A) X
  let : MonoidalClosed (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) RA) := by
    refine @Mod.monoidalClosed.{u + 1, u + 2}
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ RA inferInstance ?_
  let : SymmetricCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) RA) := by
    refine @Mod.symmetricCategory.{u + 1, u + 2}
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ RA inferInstance ?_
  let := (residueTensorColimits X RA).1
  let := (residueTensorColimits X RA).2
  let := residueFlatResolution X RA
  have hT : _root_.DerivedCategory.finiteTorAmplitude _ L ↔
      Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u} X k M := by
    have hi : _root_.DerivedCategory.finiteTorAmplitude _ (F.mapDerivedCategory.obj L) ↔
        _root_.DerivedCategory.finiteTorAmplitude _ M :=
      ⟨fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso i h,
        fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso i.symm h⟩
    have ht : _root_.DerivedCategory.finiteTorAmplitude _ L ↔
        _root_.DerivedCategory.finiteTorAmplitude _ (F.mapDerivedCategory.obj L) := by
      exact exists_congr fun a ↦ exists_congr fun b ↦
        (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff F a b L).symm
    apply ht.trans (hi.trans ?_)
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨min a b, b, (CategoryTheory.nativeTor_iff _ M (min a b) b
        (min_le_right a b)).mp
          (_root_.DerivedCategory.torAmplitudeIn.mono (min_le_left a b) le_rfl h)⟩
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, (CategoryTheory.nativeTor_iff _ M a b h.1).mpr h⟩
  exact and_congr hH hT

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
