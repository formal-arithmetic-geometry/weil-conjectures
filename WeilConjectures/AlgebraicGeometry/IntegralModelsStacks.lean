/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.IntegralCohomologicalAdicCriterion
import WeilConjectures.AlgebraicGeometry.IntegralConstantModelConstructibility
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletionTransport
import WeilConjectures.AlgebraicGeometry.IntegralModelsResidueTransport

/-! # Integral constructible objects and Stacks adic constructibility

Source: blueprint integral-models-stacks; Stacks Tag 09C1.
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

private theorem smallModules_equivalence (X : Scheme.{u})
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

private def smallDerivedIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (e : K ≅ L) : smallDerivedObject X R K ≅ smallDerivedObject X R L := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (smallRing X R))
  let F := smallModules X R
  have : F.IsEquivalence := smallModules_equivalence X R
  have : F.Additive := ⟨by intros; ext U x; rfl⟩
  change DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K)) ≅
    DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage L))
  exact (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
    F.mapDerivedCategory.mapIso ((DerivedCategory.Q.objObjPreimageIso K) ≪≫ e ≪≫
      (DerivedCategory.Q.objObjPreimageIso L).symm) ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage L)

private theorem complete_iso
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

private theorem stacksConstructible_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X))}
    (e : K ≅ L) (hK : stacksConstructible l E X K) : stacksConstructible l E X L := by
  refine ⟨complete_iso _ (smallDerivedIso X _ e) hK.1, ?_⟩
  exact residueCondition_iso l E X e hK.2

private theorem selected_equivalence
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

/-- Restriction of scalars identifies the bounded constant-model constructible category
with the Stacks adic constructible category, and reflects membership for every complex.
Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks).

Proof:
1. `det-prop-sfb-qlbar-colimit-x-integral-limit` and parts (1),(3) of
   `det-prop-integral-criterion-constant-coefficients` identify all positive quotients
   and the relative derived reductions before and after restriction.
2. `lem-weil-pbc-restriction-local-completeness` identifies local completeness for
   arbitrary complexes. `lem-weil-pbc-constant-completion-equivalence` identifies local
   and quotient-tower completeness. Its hypotheses hold since the integers are a DVR
   (`lem-weil-l-adic-extension-integers-dvr`) and the uniformizer ideal is principal.
3. Noetherian X is qcqs: apply `lem-sc-affine-noetherian-underlying-space` on a finite
   affine cover. `sk-thm-pe-constructible-comparison` and
   `det-pe-finite-tor-comparison-noetherian` identify the residue condition with a bounded
   constructible etale residue complex of finite Tor amplitude. Tensor with the unit
   in `sk-def-sfb-derived-tensor-hom` to see that finite Tor amplitude forces boundedness.
4. `lem-sfb-proetale-tor-local-global` identifies locally finite Tor dimension with a
   single global interval on this quasi-compact X, testing all modules on every slice.
5. `lem-sfb-integral-cohomological-adic-criterion` identifies bounded constant-model
   constructibility with completeness and the etale-origin residue condition. Steps
   1--4 translate these precisely into stacksConstructible of the restricted complex.
6. Part (2) of `det-prop-integral-criterion-constant-coefficients` makes restriction an
   equivalence on complete objects. Step 5 identifies the selected objects. Its
   restriction is fully faithful with unchanged Hom maps. Every adic constructible L
   has a complete preimage K, which is bounded constructible by step 5. The displayed
   natural isomorphism identifies the resulting equivalence's functor with Res.
   Section-module equivalence and AsSmall precomposition only change presentation.
-/
theorem integral_models_stacks (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (∀ K, constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K)) ∧
    ∃ e : ConstantModelBoundedConstructible (integersObj l E) X ≌
        (stacksConstructible l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksConstructible l E X).ι ≅
        (constantModelBoundedConstructible (integersObj l E) X).ι ⋙ restriction l E X) := by
  let F := IntegralConstantModel.modulesFunctor l E X
  have hc (K) : constantModelBoundedConstructible (integersObj l E) X K ↔
      (DerivedCategory.TStructure.t.bounded ((IntegralConstantModel.derived l E X).functor.obj K) ∧
        ∀ q : ℤ, Scheme.IsCompletedConstantStratified X
          (IntegralConstantCompletion.ideal l E)
          ((DerivedCategory.homologyFunctor _ q).obj
            ((IntegralConstantModel.derived l E X).functor.obj K))) := by
    apply and_congr
    · exact ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩
    · apply forall_congr'
      intro q
      let e := (F.mapDerivedCategoryHomologyFunctorIso q).app K
      exact (IntegralConstantModel.constructible_iff l E X _).trans
        ⟨fun h ↦ Scheme.completedStratified_of_iso e h,
          fun h ↦ Scheme.completedStratified_of_iso e.symm h⟩
  obtain ⟨hcomplete, e, ⟨α⟩⟩ := completion_transport l E X
  have ha (K) : Scheme.IsSfbAdicConstructible X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K) ↔
        stacksConstructible l E X ((restriction l E X).obj K) := by
    constructor
    · intro h
      exact ⟨(hcomplete K).mp h.1, (residue_transport l E X K h.1).mpr h⟩
    · intro h
      exact (residue_transport l E X K ((hcomplete K).mpr h.1)).mp h.2
  have hm (K) : constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K) :=
    (hc K).trans ((Scheme.integral_cohomological_adic_criterion l E X _).trans
      (ha K))
  refine ⟨hm, ?_⟩
  let P := constantModelBoundedConstructible (integersObj l E) X
  let PC := fun K ↦ Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal l E)
    ((IntegralConstantModel.derived l E X).functor.obj K)
  let Q := stacksConstructible l E X
  let QC := fun L ↦ ConstantCompletion.IsComplete (smallMap X (residueMap l E X))
    (smallDerivedObject X _ L)
  let : Q.IsClosedUnderIsomorphisms := ⟨fun ε h ↦ stacksConstructible_iso l E X ε h⟩
  refine selected_equivalence P PC Q QC (restriction l E X) e α ?_ ?_ ?_
  · intro K hK
    exact ((Scheme.integral_cohomological_adic_criterion l E X _).mp ((hc K).mp hK)).1
  · exact fun _ h ↦ h.1
  · exact fun K _ ↦ hm K

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
