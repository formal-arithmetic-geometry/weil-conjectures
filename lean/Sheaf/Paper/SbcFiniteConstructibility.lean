/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import all Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import all Sheaf.Paper.SbcFiniteWitnessRealization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Constructibility under the canonical quotient coefficient realization

Source: Stacks Project, Tags 03CY, 09AJ and 099Y
(blueprint: lem-sbc-finite-realization-constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

private abbrev scalarRestriction := @ConstantScalarComparison.restriction

private noncomputable def realizationUnit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (F : Sheaf J (ModuleCat.{u + 1} A)) :
    F ≅ (scalarRestriction J A R α).obj
      ((PresheafOfModules.sheafification α).obj
        ((ProEtale.finiteCoefficientModulePresheaf C A).obj F.obj)) := by
  let P := (ProEtale.finiteCoefficientModulePresheaf C A).obj F.obj
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.app P
  have : IsIso η := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    change IsIso (toSheafify J (F.obj ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))
    exact isIso_toSheafify J ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F).property
  have hi (U : Cᵒᵖ) : IsIso (η.app U) := by
    change IsIso ((PresheafOfModules.evaluation _ U).map η)
    infer_instance
  exact ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ asIso (η.app U))
    (fun f ↦ by ext x; exact PresheafOfModules.naturality_apply η f x))

private noncomputable def scalarEncoding
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    SheafOfModules.{u + 1} R ≌ Sheaf J (ModuleCat.{u + 1} A) := by
  have : (scalarRestriction J A R α).Full :=
    (ConstantScalarComparison.restrictionFullyFaithful J A R α).full
  have : (scalarRestriction J A R α).Faithful :=
    (ConstantScalarComparison.restrictionFullyFaithful J A R α).faithful
  have : (scalarRestriction J A R α).EssSurj := ⟨fun F ↦
    ⟨_, ⟨(realizationUnit J A R α F).symm⟩⟩⟩
  have : (scalarRestriction J A R α).IsEquivalence := {}
  exact (scalarRestriction J A R α).asEquivalence

private noncomputable def inverseCoefficientIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (adicLisseConstantRing X A) ≅ adicLisseConstantRing Y A := by
  have : IsIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of A)) := proEtaleConstantComparison_isIso g (CommRingCat.of A)
  exact asIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1} (CommRingCat.of A))

private noncomputable def inverseScalars {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :=
  adicLisseConstantUnit Y A ≫
    ((adicLisseForget Y).map (inverseCoefficientIso g A).inv).hom

private instance inverseScalars_injective {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallyInjective (ProEt.topology Y) (inverseScalars g A) := by
  dsimp only [inverseScalars]
  infer_instance

private instance inverseScalars_surjective {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallySurjective (ProEt.topology Y) (inverseScalars g A) := by
  dsimp only [inverseScalars]
  infer_instance

private theorem inverseScalars_square {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    adicLisseConstantUnit X A ≫ Functor.whiskerRight
        (proEtaleRingDirectImageMap g (adicLisseConstantRing X A)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (adicLisseConstantRing X A)) (Iso.refl _)).hom
        (forget₂ CommRingCat RingCat) =
      Functor.whiskerLeft (proEtaleBaseChange g).op (inverseScalars g A) := by
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  let c := inverseCoefficientIso g A
  have hc : adj.unit.app (adicLisseConstantRing X A) =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map c.inv := by
    apply (cancel_mono ((proEtaleSheafDirectImage g CommRingCat.{u + 1}).map c.hom)).mp
    rw [Category.assoc, ← Functor.map_comp, c.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hs : toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
        (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A)).hom =
      Functor.whiskerLeft (proEtaleBaseChange g).op
        (toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))) :=
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      _ _).apply_symm_apply _
  dsimp only [proEtaleRingDirectImageMap, Iso.refl_hom]
  simp only [CategoryTheory.Functor.map_id]
  change adicLisseConstantUnit X A ≫ Functor.whiskerRight
    (adj.unit.app (adicLisseConstantRing X A)).hom _ = _
  rw [hc]
  change Functor.whiskerRight
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
        (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A)).hom ≫
        Functor.whiskerLeft (proEtaleBaseChange g).op c.inv.hom)
      (forget₂ CommRingCat RingCat) = _
  rw [← Category.assoc, hs]
  rfl

private noncomputable def inverseRestrictionComparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    proEtaleRingModuleDirectImage g (adicLisseConstantRing X A)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (adicLisseConstantRing X A)) (Iso.refl _) ⋙
      scalarRestriction (ProEt.topology X) A (adicLisseRing X A)
        (adicLisseConstantUnit X A) ≅
    scalarRestriction (ProEt.topology Y) A
      ((adicLisseForget Y).obj ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (adicLisseConstantRing X A))) (inverseScalars g A) ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} A) g := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := ((proEtaleRingModuleDirectImage g (adicLisseConstantRing X A)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (adicLisseConstantRing X A)) (Iso.refl _) ⋙
        scalarRestriction (ProEt.topology X) A (adicLisseRing X A)
          (adicLisseConstantUnit X A)).obj M).obj.obj U
    let Q := ((scalarRestriction (ProEt.topology Y) A
        ((adicLisseForget Y).obj ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (adicLisseConstantRing X A))) (inverseScalars g A) ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M).obj.obj U
    change P ≅ Q
    refine (show P ≃ₗ[A] Q from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a m ↦ ?_ }).toModuleIso
    exact congrArg (fun r ↦ r •
      (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m))
      (congrArg (fun t ↦ (t.app U).hom a) (inverseScalars_square g A))
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private noncomputable def inverseImageEncoding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A]
    (M : pbcModules X (adicLisseConstantRing X A)) :
    (scalarRestriction (ProEt.topology Y) A
      ((adicLisseForget Y).obj ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (adicLisseConstantRing X A))) (inverseScalars g A)).obj
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X A)).obj M) ≅
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj
      ((scalarRestriction (ProEt.topology X) A (adicLisseRing X A)
        (adicLisseConstantUnit X A)).obj M) := by
  let EY := scalarEncoding (ProEt.topology Y) A
    ((adicLisseForget Y).obj ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (adicLisseConstantRing X A))) (inverseScalars g A)
  let EX := scalarEncoding (ProEt.topology X) A (adicLisseRing X A)
    (adicLisseConstantUnit X A)
  let L := ProEtale.upperStar (ModuleCat.{u + 1} A) g
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} A) g
  let adj := EX.toAdjunction.comp
    ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
      EY.symm.toAdjunction)
  let D := proEtaleRingModuleDirectImage g (adicLisseConstantRing X A)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (adicLisseConstantRing X A)) (Iso.refl _)
  let eR : (EY.functor ⋙ R) ⋙ EX.inverse ≅ D :=
    Functor.isoWhiskerRight (inverseRestrictionComparison g A).symm EX.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft D EX.unitIso.symm ≪≫ Functor.rightUnitor D
  let adj' := adj.ofNatIsoRight eR
  let e := (proEtaleModuleInverseImageAdjunction g (adicLisseConstantRing X A)).leftAdjointUniq
    adj'
  exact EY.functor.mapIso (e.app M) ≪≫ EY.counitIso.app (L.obj (EX.functor.obj M))

private noncomputable def restrictionChange
    (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (R S : Sheaf (ProEt.topology W) RingCat.{u + 1}) (φ : R ⟶ S)
    (α : (Functor.const W.ProEtᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    (β : (Functor.const W.ProEtᵒᵖ).obj (RingCat.of A) ⟶ S.obj)
    (h : α ≫ φ.hom = β) (M : SheafOfModules.{u + 1} S) :
    (scalarRestriction (ProEt.topology W) A R α).obj
      ((SheafOfModules.restrictScalars φ).obj M) ≅
    (scalarRestriction (ProEt.topology W) A S β).obj M := by
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ ?_) ?_)
  · let P := ((scalarRestriction (ProEt.topology W) A R α).obj
      ((SheafOfModules.restrictScalars φ).obj M)).obj.obj U
    let Q := ((scalarRestriction (ProEt.topology W) A S β).obj M).obj.obj U
    change P ≅ Q
    refine (show P ≃ₗ[A] Q from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a m ↦ ?_ }).toModuleIso
    exact congrArg (fun r ↦ r • (show M.val.obj U from m))
      (congrArg (fun t ↦ (t.app U).hom a) h)
  · intro U V f
    ext x
    rfl

private noncomputable def quotientEncoding (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ)
    (F : Sheaf (ProEt.topology W)
      (ModuleCat.{u + 1} (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))) :
    F ≅ (scalarRestriction (ProEt.topology W)
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
      (adicLisseRing W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))
      (adicLisseConstantUnit W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))).obj
      ((pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).obj
        ((pbcFunctionRealization W (pbcIntegralDatum l E) n).obj F)) := by
  let d := pbcIntegralDatum l E
  let P := ProEtale.PbcQuotient d n
  let R := (adicLisseForget W).obj ((pbcAdicRings W d).obj (op n))
  let M := (pbcFunctionRealization W d n).obj F
  exact realizationUnit (ProEt.topology W) P R (pbcFunctionScalars W d n) F ≪≫
    (restrictionChange W P (adicLisseRing W P) R
      ((adicLisseForget W).map (pbcLevelConstantComparison W d n).hom)
      (adicLisseConstantUnit W P) (pbcFunctionScalars W d n)
      (functionScalars_normalization W d n).symm M).symm

private noncomputable def fixedConstantPullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} A) g ≅
        constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A) :=
  Functor.isoWhiskerLeft _
    (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange g)
      (ModuleCat.{u + 1} A) (ProEt.topology X) (ProEt.topology Y)).symm ≪≫
    (proEtaleBaseChange g).constantSheafsheafPullbackIso (ModuleCat.{u + 1} A)
      (ProEt.topology X) (ProEt.topology Y) (ProEt.isTerminalMkId X)
      ((ProEt.isTerminalMkId X).isTerminalObj (proEtaleBaseChange g) _)

private noncomputable def inverseConstantEncoding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] (M : ModuleCat.{u + 1} A) :
    (scalarRestriction (ProEt.topology Y) A
      ((adicLisseForget Y).obj ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (adicLisseConstantRing X A))) (inverseScalars g A)).obj
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X A)).obj
        ((adicLisseConstantModules X A).obj M)) ≅
      (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj M := by
  have := ConstantScalarComparison.constantComparisonHom_isIso (ProEt.topology X) A
    (adicLisseRing X A) (adicLisseConstantUnit X A) M
  exact inverseImageEncoding g A _ ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapIso
      (asIso (ConstantScalarComparison.constantComparisonHom (ProEt.topology X) A
        (adicLisseRing X A) (adicLisseConstantUnit X A) M)).symm ≪≫
    (fixedConstantPullback g A).app M

private theorem relativeFinite_of_encoding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A]
    (F : pbcModules X (adicLisseConstantRing X A))
    (hF : ProEtale.IsFiniteLocallyConstant A
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj
        ((scalarRestriction (ProEt.topology X) A (adicLisseRing X A)
          (adicLisseConstantUnit X A)).obj F))) :
    IsRelativelyFiniteLisseModule g A
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X A)).obj F) := by
  let R := (adicLisseForget Y).obj
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (adicLisseConstantRing X A))
  let α := inverseScalars g A
  let N := (proEtaleModuleInverseImage g (adicLisseConstantRing X A)).obj F
  let H := (scalarRestriction (ProEt.topology Y) A R α).obj N
  have hH := ProEtale.isFiniteLocallyConstant_of_iso (inverseImageEncoding g A F).symm hF
  obtain ⟨I, U, f, hf, hm⟩ := ProEtale.finiteModels_over A H hH
  let v₀ := (ProEt.isTerminalMkId Y).from (⊤_ Y.ProEt)
  refine ⟨(Sieve.generate (Presieve.ofArrows U f)).pullback v₀,
    (ProEt.topology Y).pullback_stable v₀
      (Precoverage.generate_mem_toGrothendieck hf), ?_⟩
  let J := ProEt.topology Y
  intro V v hv
  obtain ⟨Z, a, b, ⟨j⟩, he⟩ := hv
  obtain ⟨M, hM, ⟨e⟩⟩ := hm j
  let Q := (Over.map a).sheafPushforwardContinuous (ModuleCat.{u + 1} A)
    (J.over V) (J.over (U j))
  let cU := constantSheafOverIso J (ModuleCat.{u + 1} A) (U j) M
  let cV := constantSheafOverIso J (ModuleCat.{u + 1} A) V M
  let eV : H.over V ≅
      (constantSheaf (J.over V) (ModuleCat.{u + 1} A)).obj M :=
    (H.pushforwardOverMapIso a).symm ≪≫ Q.mapIso (e ≪≫ cU) ≪≫
      (Sheaf.pushforwardOverMapIso _ a) ≪≫ cV.symm
  let αV := Functor.whiskerLeft (Over.forget V).op α
  have : Presheaf.IsLocallySurjective (J.over V) αV :=
    Presheaf.isLocallySurjective_whisker _ J (Over.forget V) α
  let t := inverseConstantEncoding g A M
  let tV := (J.overPullback (ModuleCat.{u + 1} A) V).mapIso t ≪≫
    cV.symm
  exact ⟨M, hM, ⟨(ConstantScalarComparison.restrictionFullyFaithful
    (J.over V) A (R.over V) αV).preimageIso (eV ≪≫ tV.symm)⟩⟩

/-- Realization preserves intrinsic finite constructibility, without an etale-origin
assumption. Source: Stacks Project, Tags 03CY, 09AJ and 099Y.
(blueprint: lem-sbc-finite-realization-constructibility).

Proof: keep the given positive finite constructible locally closed stratification.
On each stratum, local constancy and finite geometric stalks give finite constant
models by lem-sf-proetale-lisse-finite-models. Realization and restriction along the
canonical constant-to-function quotient comparison identify fixed constant modules
with adicLisseConstantModules. They commute with restriction to a stratum and to a
slice, by the constant-section coefficient square and uniqueness of inverse image.
Thus each finite fixed constant model is a finite constant module model for the
actual inverse-image coefficient sheaf. The same covering sieve and same finite
modules prove relative finite lissity on every stratum. No common stratification
across different sheaves and no nonempty-scheme assumption are used. -/
theorem sbcFiniteRealization_constructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ)
    (F : Sheaf (ProEt.topology W)
      (ModuleCat.{u + 1} (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)))
    (hF : IsConstructibleProEtaleFixedModuleSheaf W
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) F) :
    IsConstructibleProEtaleCoefficientModuleSheaf W
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
      ((pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).obj
        ((pbcFunctionRealization W (pbcIntegralDatum l E) n).obj F))  := by
  obtain ⟨S, hn, hS, hF⟩ := hF
  refine ⟨S, hn, hS, fun i ↦ ?_⟩
  apply relativeFinite_of_encoding
  exact ProEtale.isFiniteLocallyConstant_of_iso
    ((ProEtale.upperStar _ (S.immersion i)).mapIso (quotientEncoding l E W n F))
      (finite_models_of_fixed_lisse (S.domain i) _ _ (hF i))

end WeilConjectures
