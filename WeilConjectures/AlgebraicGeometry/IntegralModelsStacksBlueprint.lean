/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeartClosure
import WeilConjectures.SixFunctors.ProEtale.InternalCompletionStacksComparison
import WeilConjectures.SixFunctors.ProEtale.InternalResidueStacksComparison

/-! # Integral models and Stacks adic constructibility along the current blueprint

**Work in progress.** This file is a skeleton for re-proving `det-lem-integral-models-stacks`
along the current blueprint. It is imported by no other module, and its three inputs
(`internal_integral_criterion_forward`, `internal_integral_criterion_reverse`,
`restriction_complete_equivalence`) are still `sorry`. The theorem itself is proved in
`WeilConjectures.AlgebraicGeometry.IntegralModelsStacks` through the legacy adic tower.

The current blueprint proves `det-lem-integral-models-stacks` by restriction of scalars along
the map from the constant coefficient ring, using the integral constructibility criterion
`sk-prop-integral-criterion`, the constant-coefficient criterion
`det-prop-integral-criterion-constant-coefficients` and the pro-etale/etale comparison of
constructible complexes. This file states the criterion in the internal presentation and
assembles the comparison from it. The assembled theorem has exactly the statement of
`IntegralModelsStacks.integral_models_stacks`; it replaces that proof once the stated inputs
are proved.

Source: blueprint det-lem-integral-models-stacks; Stacks Tag 09C1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- Local derived completeness for the first residue map, transported to the small site:
the completeness clause of `stacksConstructible`.
Source: Stacks Tag 09C1 (auxiliary; not a blueprint node). -/
def stacksComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X))) :=
  fun L ↦ ConstantCompletion.IsComplete (smallMap X (residueMap l E X))
    (smallDerivedObject X _ L)

/-- The complexes over the continuous integers whose restriction to the constant integers is
complete in the sense of `stacksComplete`.
Source: blueprint det-lem-integral-models-stacks
(auxiliary; not a blueprint node). -/
def restrictionComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :=
  fun K ↦ stacksComplete l E X ((restriction l E X).obj K)

/-- Integral constructibility criterion, direction (1) to (2), in the internal presentation:
a bounded constructible complex over the continuous integers is derived complete, and its
first derived reduction is bounded constructible of finite Tor amplitude.
Source: blueprint sk-prop-integral-criterion, proof of (1) implies (2)
(auxiliary; not a blueprint node). -/
theorem internal_integral_criterion_forward
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K) :
    IsDerivedComplete l E X K ∧
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) ∧
      DerivedCategory.finiteTorAmplitude _
        ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  sorry

/-- Integral constructibility criterion, direction (2) to (1), in the internal presentation:
a derived complete complex whose first derived reduction is bounded constructible is bounded
constructible over the continuous integers.
Source: blueprint sk-prop-integral-criterion, (2) implies (3) implies (1), using
sk-prop-integral-local-structure (auxiliary; not a blueprint node). -/
theorem internal_integral_criterion_reverse
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hc : IsDerivedComplete l E X K)
    (hr : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
      ((AdicCompletion.derivedReduction l E X 0).obj K)) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K := by
  sorry

/-- Restriction of scalars along the map from the constant integer ring is an equivalence from
the complexes whose restriction is complete onto the complete complexes, with the inclusion
functors identified with restriction.
Source: blueprint det-prop-integral-criterion-constant-coefficients (2), (3) and
det-lem-integral-models-stacks (auxiliary; not a blueprint node). -/
theorem restriction_complete_equivalence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) [IsNoetherian X] :
    ∃ e : (restrictionComplete l E X).FullSubcategory ≌ (stacksComplete l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksComplete l E X).ι ≅
        (restrictionComplete l E X).ι ⋙ restriction l E X) := by
  sorry

private theorem bp_smallModules_equivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).IsEquivalence := by
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R)
  let B := ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj A
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsContinuous
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
        X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (J := Scheme.ProEt.topology X)
    (K := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  exact inferInstanceAs
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor ⋙ e.inverse).IsEquivalence

private def bp_smallDerivedIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (e : K ≅ L) : smallDerivedObject X R K ≅ smallDerivedObject X R L := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (smallRing X R))
  let F := smallModules X R
  have : F.IsEquivalence := bp_smallModules_equivalence X R
  have : F.Additive := ⟨by intros; ext U x; rfl⟩
  change DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K)) ≅
    DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage L))
  exact (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
    F.mapDerivedCategory.mapIso ((DerivedCategory.Q.objObjPreimageIso K) ≪≫ e ≪≫
      (DerivedCategory.Q.objObjPreimageIso L).symm) ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage L)

private theorem bp_complete_iso
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {O S : Sheaf J CommRingCat.{u + 1}} (q : O ⟶ S)
    {K L : ConstantCompletion.D O} (e : K ≅ L)
    (hK : ConstantCompletion.IsComplete q K) : ConstantCompletion.IsComplete q L := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod O)
  let (U : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (O.over U))
  intro U f hf
  let H := (Functor.curry.obj (derivedInternalHom (J.over U) (O.over U))).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))))
  exact (((ringedDerivedRestriction O U ⋙ H).mapIso e).isZero_iff).mp (hK U f hf)

private theorem bp_stacksConstructible_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X))}
    (e : K ≅ L) (hK : stacksConstructible l E X K) : stacksConstructible l E X L :=
  ⟨bp_complete_iso _ (bp_smallDerivedIso X _ e) hK.1, residueCondition_iso l E X e hK.2⟩

private theorem bp_selected_equivalence
    {C D : Type*} [Category C] [Category D]
    (P PC : ObjectProperty C) (Q QC : ObjectProperty D)
    (F : C ⥤ D) (e : PC.FullSubcategory ≌ QC.FullSubcategory)
    (α : e.functor ⋙ QC.ι ≅ PC.ι ⋙ F)
    (hP : P ≤ PC) (hQ : Q ≤ QC)
    [Q.IsClosedUnderIsomorphisms]
    (hm : ∀ K, PC K → (P K ↔ Q (F.obj K))) :
    ∃ d : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (d.functor ⋙ Q.ι ≅ P.ι ⋙ F) := by
  let i := ObjectProperty.ιOfLE hP
  let G := Q.lift (P.ι ⋙ F) (fun K ↦ (hm K.obj (hP _ K.property)).mp K.property)
  let β : i ⋙ e.functor ⋙ QC.ι ≅ G ⋙ Q.ι := Functor.isoWhiskerLeft i α
  let h := ((Functor.FullyFaithful.ofFullyFaithful i).comp
    ((Functor.FullyFaithful.ofFullyFaithful e.functor).comp
      QC.fullyFaithfulι)).ofIso β
  let hG := Functor.FullyFaithful.ofCompFaithful h
  let : G.Full := hG.full
  let : G.Faithful := hG.faithful
  have : G.EssSurj := by
    constructor
    intro L
    let L' : QC.FullSubcategory := ⟨L.obj, hQ _ L.property⟩
    let K := e.inverse.obj L'
    let γ : F.obj K.obj ≅ L.obj :=
      (α.app K).symm ≪≫ QC.ι.mapIso (e.counitIso.app L')
    have hK : P K.obj := (hm K.obj K.property).mpr (Q.prop_of_iso γ.symm L.property)
    exact ⟨⟨K.obj, hK⟩, ⟨Q.fullyFaithfulι.preimageIso γ⟩⟩
  let : G.IsEquivalence := {}
  exact ⟨G.asEquivalence, ⟨Iso.refl _⟩⟩

/-- The criterion part of `det-lem-integral-models-stacks`: a complex over the continuous
integers is bounded constructible iff its restriction is Stacks adic constructible.
Source: blueprint det-lem-integral-models-stacks; Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks).

Proof: transport along `pointComparison` to the internal presentation, apply the two
directions of the integral criterion, and identify completeness and the residue clause by
`internal_completion_stacks_comparison` and `internal_residue_stacks_comparison`. -/
theorem integral_models_stacks_criterion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :
    constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K) := by
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).hom.hom X)
  let K' := G.mapDerivedCategory.obj K
  let eK : F.mapDerivedCategory.obj K' ≅ K :=
    ((Functor.mapDerivedCategoryCompIso G F).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        ((Mod.comapComp
          (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
          (coefficientMap (IntegralConstantModel.pointComparison l E).hom.hom X)).symm ≪≫
          Mod.comapCongr (by
            rw [← coefficientMap_comp]
            exact (congrArg (upperStarFromPoint X).map (congrArg Mon.Hom.hom
              (IntegralConstantModel.pointComparison l E).inv_hom_id)).trans
              ((upperStarFromPoint X).map_id _)) ≪≫ Mod.comapId _) ≪≫
      Functor.mapDerivedCategoryIdIso _).app K
  have hi := (constantModelConstructibleFiniteTor_wellDefined (integersObj l E) X).2.1
  have hP : constantModelBoundedConstructible (integersObj l E) X K ↔
      constantModelBoundedConstructible (integersObj l E) X (F.mapDerivedCategory.obj K') :=
    ⟨fun h ↦ (constantModelBoundedConstructible _ X).prop_of_iso eK.symm h,
      fun h ↦ (constantModelBoundedConstructible _ X).prop_of_iso eK h⟩
  have hF : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have hc : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K' ↔
      constantModelBoundedConstructible (integersObj l E) X (F.mapDerivedCategory.obj K') := by
    apply and_congr
    · exact ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩
    · apply forall_congr'
      intro q
      have h := constantModel_comap_iff (IntegralConstantModel.pointComparison l E).inv.hom
        X ((DerivedCategory.homologyFunctor _ q).obj K')
      have hi' := (constantModelConstructibleFiniteTor_wellDefined (integersObj l E) X).1
      let := hi'
      exact h.symm.trans
        ⟨fun h ↦ ObjectProperty.prop_of_iso _
          ((F.mapDerivedCategoryHomologyFunctorIso q).app K') h,
        fun h ↦ ObjectProperty.prop_of_iso _
          ((F.mapDerivedCategoryHomologyFunctorIso q).app K').symm h⟩
  have hint : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K' ↔
      stacksConstructible l E X ((restriction l E X).obj (F.mapDerivedCategory.obj K')) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨h1, h2⟩ := internal_integral_criterion_forward l E X K' h
      exact ⟨(internal_completion_stacks_comparison l E X K').mp h1,
        (internal_residue_stacks_comparison l E X K').mpr h2⟩
    · have h2 := (internal_residue_stacks_comparison l E X K').mp h.2
      exact internal_integral_criterion_reverse l E X K'
        ((internal_completion_stacks_comparison l E X K').mpr h.1) h2.1
  have hQ : stacksConstructible l E X ((restriction l E X).obj (F.mapDerivedCategory.obj K')) ↔
      stacksConstructible l E X ((restriction l E X).obj K) :=
    ⟨bp_stacksConstructible_iso l E X ((restriction l E X).mapIso eK),
      bp_stacksConstructible_iso l E X ((restriction l E X).mapIso eK).symm⟩
  exact hP.trans (hc.symm.trans (hint.trans hQ))

/-- `det-lem-integral-models-stacks` assembled along the current blueprint route; the
statement is that of `integral_models_stacks`.
Source: blueprint det-lem-integral-models-stacks; Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks).

Proof: the criterion is `integral_models_stacks_criterion`. Restriction is an equivalence
from the complexes with complete restriction onto the complete complexes
(`restriction_complete_equivalence`); bounded constructible complexes have complete
restriction and Stacks adic constructible complexes are complete, so the equivalence
restricts to the selected full subcategories with the same functor. -/
theorem integral_models_stacks_blueprint (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (∀ K, constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K)) ∧
    ∃ e : ConstantModelBoundedConstructible (integersObj l E) X ≌
        (stacksConstructible l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksConstructible l E X).ι ≅
        (constantModelBoundedConstructible (integersObj l E) X).ι ⋙ restriction l E X) := by
  have hm := integral_models_stacks_criterion l E X
  refine ⟨hm, ?_⟩
  obtain ⟨e, ⟨α⟩⟩ := restriction_complete_equivalence l E X
  let : (stacksConstructible l E X).IsClosedUnderIsomorphisms :=
    ⟨fun ε h ↦ bp_stacksConstructible_iso l E X ε h⟩
  exact bp_selected_equivalence (constantModelBoundedConstructible (integersObj l E) X)
    (restrictionComplete l E X) (stacksConstructible l E X) (stacksComplete l E X)
    (restriction l E X) e α
    (fun K hK ↦ ((hm K).mp hK).1) (fun _ h ↦ h.1) (fun K _ ↦ hm K)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
