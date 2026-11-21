/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeartClosure
import WeilConjectures.SixFunctors.ProEtale.InternalFirstResidueReductionComparison
import WeilConjectures.AlgebraicGeometry.DiscreteFieldTorAmplitude
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Actual residue reduction under constant scalar restriction

## References

* [Stacks, Tag 099L](https://stacks.math.columbia.edu/tag/099L)
* [Stacks, Tag 09C1](https://stacks.math.columbia.edu/tag/09C1)
* [Stacks, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks, Tag 0651](https://stacks.math.columbia.edu/tag/0651)
* [Stacks, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* Bhatt–Scholze, *The pro-étale topology for schemes*, Remark 6.3.2
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

local instance residueSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

local instance residueAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

local instance residueAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify in
/-- Constant scalar restriction identifies the first-residue constructible Tor condition. -/
theorem internal_residue_stacks_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    IntegralModelsStacks.residueCondition.{u} l E X
      ((IntegralModelsStacks.restriction l E X).obj
          ((Mod.comap (coefficientMap
            (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory.obj K)) ↔
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
      ((AdicCompletion.derivedReduction l E X 0).obj K) ∧
    _root_.DerivedCategory.finiteTorAmplitude _
      ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  obtain ⟨e, ⟨c⟩⟩ := internal_first_residue_reduction_comparison l E X
  let R := DerivedNakayama.quotientRing l E 1
  let S := IntegralModelsStacks.discreteObj (Padic.coefficientExtensionRing l E 1)
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap e.inv.hom X)
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  let L := (AdicCompletion.derivedReduction l E X 0).obj K
  let M := ((Mod.extendScalars (IntegralModelsStacks.residueMap l E X)).leftDerivedFunctor).obj
    ((IntegralModelsStacks.restriction l E X).obj
      ((Mod.comap (coefficientMap
        (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory.obj K))
  have hH : (∀ n : ℤ, IsConstantModelConstructible S X
      ((DerivedCategory.homologyFunctor _ n).obj M)) ↔
      ∀ n : ℤ, IsConstantModelConstructible R X
        ((DerivedCategory.homologyFunctor _ n).obj L) := by
    apply forall_congr'
    intro n
    let h := (DerivedCategory.homologyFunctor _ n).mapIso (c.app K)
    let a := (F.mapDerivedCategoryHomologyFunctorIso n).app L
    exact (show IsConstantModelConstructible S X
        ((DerivedCategory.homologyFunctor _ n).obj M) ↔
      IsConstantModelConstructible S X
        (F.obj ((DerivedCategory.homologyFunctor _ n).obj L)) from
      ⟨fun hM ↦ constantModelConstructible_transport _ (h ≪≫ a.symm) hM,
        fun hM ↦ constantModelConstructible_transport _ (h ≪≫ a.symm).symm hM⟩).trans
      (constantModel_comap_iff e.inv.hom X _)
  have hT : _root_.DerivedCategory.finiteTorAmplitude _ M ↔
      _root_.DerivedCategory.finiteTorAmplitude _ L := by
    have hi : _root_.DerivedCategory.finiteTorAmplitude _ M ↔
        _root_.DerivedCategory.finiteTorAmplitude _ (F.mapDerivedCategory.obj L) :=
      ⟨fun hM ↦ ObjectProperty.prop_of_iso _ (c.app K) hM,
        fun hL ↦ ObjectProperty.prop_of_iso _ (c.app K).symm hL⟩
    apply hi.trans
    constructor
    · rintro ⟨a, b, hab⟩
      exact ⟨a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff F a b L).mp hab⟩
    · rintro ⟨a, b, hab⟩
      exact ⟨a, b, DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj F hab⟩
  change ((∀ n : ℤ, IsConstantModelConstructible S X
    ((DerivedCategory.homologyFunctor _ n).obj M)) ∧
    _root_.DerivedCategory.finiteTorAmplitude _ M) ↔ _
  rw [hH, hT]
  constructor
  · rintro ⟨hH, hT⟩
    refine ⟨⟨?_, hH⟩, hT⟩
    obtain ⟨a, b, hab⟩ := hT
    exact (DerivedCategory.exists_homologyConcentratedIn_iff_bounded L).mp
      ⟨a, b, DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hab⟩
  · exact fun h ↦ ⟨h.1.2, h.2⟩

/-- The first residue ring `𝒪_E/ϖ_E` is a field: `ϖ_E` generates the maximal ideal. -/
@[implicit_reducible]
noncomputable def coefficientExtensionRingOneField (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Field (Padic.coefficientExtensionRing l E 1) :=
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
    rw [Padic.coefficientExtensionIdeal, pow_one, hgen]
    exact h.2.2.2.2.1
  Ideal.Quotient.field _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify in
/-- A bounded constructible complex over the first residue ring `𝒪_E/ϖ_E` has finite Tor
amplitude. Hence the finite Tor clause of the integral constructibility criterion holds
automatically, `𝒪_E/ϖ_E` being a field. -/
theorem finiteTorAmplitude_of_constantModelBoundedConstructible_residue
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    {L : AdicCompletion.FiniteDerived l E X 0}
    (hL : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X L) :
    _root_.DerivedCategory.finiteTorAmplitude _ L := by
  obtain ⟨e, -⟩ := internal_first_residue_reduction_comparison l E X
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap e.inv.hom X)
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  let := coefficientExtensionRingOneField l E
  obtain ⟨a, b, h⟩ := IntegralModelsStacks.finiteTorAmplitude_of_discreteField X
    (Padic.coefficientExtensionRing l E 1) (F.bounded_mapDerivedCategory_obj hL.1)
  exact ⟨a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff F a b L).mp h⟩

end AlgebraicGeometry.ProEtale
