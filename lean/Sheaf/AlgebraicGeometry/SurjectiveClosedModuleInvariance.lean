/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.ConstructibleSheaf.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import all Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

/-!
# Surjective closed immersions and ordinary module sheaves

Source: Stacks Project, Tag 09AB (lemma-thickening), Tag 04DZ
(theorem-topological-invariance), and Modules on Sites, lemma-pullback-locally-constant
(blueprint: lem-sfb-surjective-closed-module-invariance).

The two local-model predicates expand the finite and finite-projective clauses of this
node. They use the existing constant sheaves and localized restrictions. The Boolean
selects whether a finite-free splitting is required; it does not change the chosen site.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The finite local models in this node on the etale site. For `projective = true`,
each model is explicitly a retract of a finite free module; for `false`, only finiteness
is required. This refines the existing `LocallyConstantDatum`, with the same covers and
localized constant module sheaves, rather than using a stalk-finiteness surrogate.
Source: Stacks, Modules on Sites, lemma-pullback-locally-constant, with the finite-model
clause of blueprint det-sf-flat-model-generation
(blueprint: lem-sfb-surjective-closed-module-invariance). -/
def sfbEtaleFiniteLocalModels {Y : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (projective : Bool) : Prop :=
  ∃ d : LocallyConstantDatum H, ∀ j : d.cover.I₀,
    ∃ M : ModuleCat.{u + 1} A, Finite M ∧
      Nonempty (H.over (d.cover.etalePrecoverageToEtale j) ≅
        (constantSheaf
          (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale j))
          (ModuleCat.{u + 1} A)).obj M) ∧
      (projective = true → ∃ (n : ℕ) (i : M →ₗ[A] (Fin n → A))
        (r : (Fin n → A) →ₗ[A] M), r.comp i = LinearMap.id)

/-- The finite local models in this node on the original small pro-etale ringed site.
This is the covering datum of `IsLocallyConstantProEtaleModuleSheaf` with finite models,
and, when requested, explicit finite-free splittings. No etale-origin condition occurs.
Source: Stacks, Modules on Sites, lemma-pullback-locally-constant, and Tag 09AB;
blueprint det-sf-flat-model-generation, clause (2)
(blueprint: lem-sfb-surjective-closed-module-invariance). -/
def sfbProEtaleFiniteLocalModels (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (projective : Bool) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → Y.ProEt)
    (f : ∀ j : I, U j ⟶ ProEt.mk (𝟙 Y)),
    Presieve.ofArrows U f ∈ (ProEt.precoverage Y).coverings _ ∧
      ∀ j : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A), Finite M ∧
        Nonempty (H.over (U j) ≅ proEtaleConstantModuleSheafOver Y A (U j) M) ∧
        (projective = true → ∃ (n : ℕ)
          (i : M →ₗ[ULift.{u + 1, u} A] (Fin n → ULift.{u + 1, u} A))
          (r : (Fin n → ULift.{u + 1, u} A) →ₗ[ULift.{u + 1, u} A] M),
          r.comp i = LinearMap.id)

private theorem sfbEtale_over_model_iff {Y : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A]
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (U : Y.Etale)
    (M : ModuleCat.{u + 1} A) :
    Nonempty (H.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} A)).obj M) ↔
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) U.hom).obj H ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) := by
  let E := Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
  let e := overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U H
  let c := (Etale.overEquiv U).constantSheafSheafCongrIso
    (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} A)
    CategoryTheory.Over.mkIdTerminal
  constructor
  · rintro ⟨i⟩
    exact ⟨e.symm ≪≫ E.functor.mapIso i ≪≫ c.app M⟩
  · rintro ⟨i⟩
    exact ⟨E.functor.preimageIso (e ≪≫ i ≪≫ (c.app M).symm)⟩

/-- Surjective closed restriction on the etale site: the actual adjunction is an
adjoint equivalence, constants pull back to the same module models, and finite local
models, with or without finite-free splittings, are preserved and reflected.
Source: Stacks, Tags 04DZ, 03SI and Modules on Sites, lemma-pullback-locally-constant
(blueprint: lem-sfb-surjective-closed-module-invariance).

Proof: a surjective closed immersion is a universal homeomorphism. The existing
etale topological-invariance theorem applies directly to ModuleCat-valued sheaves,
so both functors are equivalences and the actual adjunction unit and counit are
isomorphisms. The constant comparison is upperStarConstantSheafIso.
For preservation, pull back a trivializing cover and each chosen module isomorphism.
The composition comparisons identify the two pullbacks around the cartesian square;
the constant comparison retains the exact same module M.
For reflection, lift each member of a trivializing cover through the equivalence of
etale sites. The lifts cover Y: lift a point to T, then to a cover member and project
its image in the corresponding fiber product to the lifted member over Y.
On each lifted member, pull the given trivialization back along the isomorphism to
the original member. The composition comparisons identify its source with the
pullback of H. The base-changed universal homeomorphism has fully faithful module
inverse image, so preimageIso descends the trivialization with the same model M.
The localization equivalence and its constant-sheaf comparison convert between
the localized-site and scheme-site presentations throughout. All finiteness proofs,
integers n and splitting maps are reused unchanged. The cover arguments quantify
over points, so empty covers and schemes need no exception. -/
theorem sfbEtale_surjectiveClosed_module_invariance
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit ∧
    IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).counit ∧
    (Etale.upperStar (ModuleCat.{u + 1} A) h).IsEquivalence ∧
    (Etale.lowerStar (ModuleCat.{u + 1} A) h).IsEquivalence ∧
    (∀ M : ModuleCat.{u + 1} A,
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) h).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) ≅
          (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)) ∧
    (∀ (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (projective : Bool),
      sfbEtaleFiniteLocalModels A H projective ↔
        sfbEtaleFiniteLocalModels A
          ((Etale.upperStar (ModuleCat.{u + 1} A) h).obj H) projective) := by
  have : (Etale.upperStar (ModuleCat.{u + 1} A) h).IsEquivalence :=
    Etale.isEquivalence_upperStar _ h
  have : (Etale.lowerStar (ModuleCat.{u + 1} A) h).IsEquivalence :=
    Etale.isEquivalence_lowerStar _ h
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro M
    exact ⟨(upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).app M⟩
  · intro H projective
    have : JointlySurjective etalePrecoverage.{u} :=
      inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
    constructor
    · rintro ⟨d, hd⟩
      let D := ModuleCat.{u + 1} A
      let G := (Etale.upperStar D h).obj H
      have hm (j : d.cover.I₀) :
          ∃ M : D, Finite M ∧
            Nonempty (G.over (Cover.etalePrecoverageToEtale (d.cover.pullback₂ h) j) ≅
              (constantSheaf
                (T.smallEtaleTopology.over (Cover.etalePrecoverageToEtale (d.cover.pullback₂ h) j))
                D).obj M) ∧
            (projective = true → ∃ (n : ℕ) (i : M →ₗ[A] (Fin n → A))
              (r : (Fin n → A) →ₗ[A] M), r.comp i = LinearMap.id) := by
        obtain ⟨M, hM, eM, hp⟩ := hd j
        obtain ⟨iM⟩ := (sfbEtale_over_model_iff A H _ M).mp eM
        let e : (Etale.upperStar D (Limits.pullback.fst (d.cover.f j) h)).obj
            ((Etale.upperStar D (d.cover.f j)).obj H) ≅
            (Etale.upperStar D (Limits.pullback.snd (d.cover.f j) h)).obj G :=
          ((Etale.upperStarComp D (Limits.pullback.fst (d.cover.f j) h)
            (d.cover.f j)).app H).symm ≪≫
            eqToIso (congrArg (fun m ↦ (Etale.upperStar D m).obj H) Limits.pullback.condition) ≪≫
            (Etale.upperStarComp D (Limits.pullback.snd (d.cover.f j) h) h).app H
        let iG := e.symm ≪≫
          (Etale.upperStar D (Limits.pullback.fst (d.cover.f j) h)).mapIso iM ≪≫
          (upperStarConstantSheafIso D (Limits.pullback.fst (d.cover.f j) h)).app M
        exact ⟨M, hM, (sfbEtale_over_model_iff A G _ M).mpr ⟨iG⟩, hp⟩
      refine ⟨⟨d.cover.pullback₂ h, ?_⟩, hm⟩
      intro j
      obtain ⟨M, _, ⟨iM⟩, _⟩ := hm j
      exact Sheaf.isConstant_of_iso _ iM
    · rintro ⟨d, hd⟩
      let D := ModuleCat.{u + 1} A
      let G := (Etale.upperStar D h).obj H
      let V (i : d.cover.I₀) : Y.Etale :=
        h.Etale.objPreimage (d.cover.etalePrecoverageToEtale i)
      let e (i : d.cover.I₀) : h.Etale.obj (V i) ≅ d.cover.etalePrecoverageToEtale i :=
        h.Etale.objObjPreimageIso _
      have hinv (i : d.cover.I₀) :
          (e i).inv.left ≫ Limits.pullback.snd (V i).hom h = d.cover.f i :=
        MorphismProperty.Over.w (e i).inv
      let C : Cover.{u} etalePrecoverage Y :=
        { I₀ := d.cover.I₀
          X i := (V i).left
          f i := (V i).hom
          mem₀ := by
            refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun y ↦ ?_, fun i ↦ (V i).prop⟩
            obtain ⟨x, rfl⟩ := h.surjective y
            obtain ⟨i, x', rfl⟩ := d.cover.exists_eq x
            refine ⟨i, (Limits.pullback.fst (V i).hom h) ((e i).inv.left x'), ?_⟩
            change ((e i).inv.left ≫ Limits.pullback.fst (V i).hom h ≫ (V i).hom) x' =
              (d.cover.f i ≫ h) x'
            rw [Limits.pullback.condition, ← Category.assoc, hinv]
            rfl }
      have hm (i : d.cover.I₀) :
          ∃ M : D, Finite M ∧
            Nonempty (H.over (C.etalePrecoverageToEtale i) ≅
              (constantSheaf (Y.smallEtaleTopology.over (C.etalePrecoverageToEtale i)) D).obj M) ∧
            (projective = true → ∃ (n : ℕ) (j : M →ₗ[A] (Fin n → A))
              (r : (Fin n → A) →ₗ[A] M), r.comp j = LinearMap.id) := by
        obtain ⟨M, hM, eM, hp⟩ := hd i
        obtain ⟨iM⟩ := (sfbEtale_over_model_iff A G _ M).mp eM
        have hsnd : Limits.pullback.snd (V i).hom h = (e i).hom.left ≫ d.cover.f i :=
          (MorphismProperty.Over.w (e i).hom).symm
        let e' : (Etale.upperStar D (Limits.pullback.fst (V i).hom h)).obj
            ((Etale.upperStar D (V i).hom).obj H) ≅
            (Etale.upperStar D (e i).hom.left).obj
              ((Etale.upperStar D (d.cover.f i)).obj G) :=
          ((Etale.upperStarComp D (Limits.pullback.fst (V i).hom h) (V i).hom).app H).symm ≪≫
            eqToIso (congrArg (fun m ↦ (Etale.upperStar D m).obj H) Limits.pullback.condition) ≪≫
            (Etale.upperStarComp D (Limits.pullback.snd (V i).hom h) h).app H ≪≫
            eqToIso (congrArg (fun m ↦ (Etale.upperStar D m).obj G) hsnd) ≪≫
            (Etale.upperStarComp D (e i).hom.left (d.cover.f i)).app G
        have : (Etale.upperStar D (Limits.pullback.fst (V i).hom h)).IsEquivalence :=
          Etale.isEquivalence_upperStar D _
        let iV := (Etale.upperStar D (Limits.pullback.fst (V i).hom h)).preimageIso
          (e' ≪≫ (Etale.upperStar D (e i).hom.left).mapIso iM ≪≫
            (upperStarConstantSheafIso D (e i).hom.left).app M ≪≫
            ((upperStarConstantSheafIso D (Limits.pullback.fst (V i).hom h)).app M).symm)
        exact ⟨M, hM, (sfbEtale_over_model_iff A H _ M).mpr ⟨iV⟩, hp⟩
      refine ⟨⟨C, ?_⟩, hm⟩
      intro i
      obtain ⟨M, _, ⟨iM⟩, _⟩ := hm i
      exact Sheaf.isConstant_of_iso _ iM

private theorem sfbProEtale_over_model_iff {Y : Scheme.{u}}
    (A : Type u) [CommRing A]
    (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEt)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    Nonempty (H.over U ≅ proEtaleConstantModuleSheafOver Y A U M) ↔
      Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U.hom).obj
        ((proEtaleModuleRestriction Y A).obj H) ≅
          (constantSheaf (ProEt.topology U.left)
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj M) := by
  let D := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let R := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)
  let a := Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit Y A)
  have : Presheaf.IsLocallyInjective ((ProEt.topology Y).over U) a :=
    (proEtaleConstantRingUnit_over_locallyBijective Y A U).1
  have : Presheaf.IsLocallySurjective ((ProEt.topology Y).over U) a :=
    (proEtaleConstantRingUnit_over_locallyBijective Y A U).2
  let E := ConstantScalarComparison.restriction ((ProEt.topology Y).over U)
    (ULift.{u + 1, u} A) (R.over U) a
  have hc := ConstantScalarComparison.constantComparisonHom_isIso
    ((ProEt.topology Y).over U) (ULift.{u + 1, u} A) (R.over U) a M
  let c := asIso (ConstantScalarComparison.constantComparisonHom
    ((ProEt.topology Y).over U) (ULift.{u + 1, u} A) (R.over U) a M)
  have : (ProEt.sliceEquiv Y U).inverse.IsDenseSubsite
      (ProEt.topology U.left) ((ProEt.topology Y).over U) := ProEt.sliceDense Y U
  let S := (ProEt.sliceEquiv Y U).sheafCongr
    ((ProEt.topology Y).over U) (ProEt.topology U.left) D
  let G := (proEtaleModuleRestriction Y A).obj H
  let r : S.functor.obj (G.over U) ≅
      (ProEtale.localizationRestriction D U.hom U.prop).obj G :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let k := ((ProEt.sliceEquiv Y U).constantSheafSheafCongrIso
    ((ProEt.topology Y).over U) (ProEt.topology U.left) D
    (Over.mkIdTerminal (X := U))).app M
  let t := (ProEtale.upperStarIsoLocalizationRestriction D U.hom U.prop).app G
  constructor
  · rintro ⟨e⟩
    exact ⟨t ≪≫ r.symm ≪≫ S.functor.mapIso (E.mapIso e ≪≫ c.symm) ≪≫ k⟩
  · rintro ⟨e⟩
    let e' := S.functor.preimageIso (r ≪≫ t.symm ≪≫ e ≪≫ k.symm)
    exact ⟨(ConstantScalarComparison.restrictionFullyFaithful
      ((ProEt.topology Y).over U) (ULift.{u + 1, u} A) (R.over U) a).preimageIso (e' ≪≫ c)⟩

private noncomputable def sfbProEtale_constant_comparison (Y : Scheme.{u})
    (A : Type u) [CommRing A] (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj M ≅
      (proEtaleModuleRestriction Y A).obj (proEtaleConstantModuleSheaf Y A M) := by
  let R := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)
  have : Presheaf.IsLocallyInjective (ProEt.topology Y) (proEtaleModuleScalarUnit Y A) :=
    (proEtaleConstantRingUnit_locallyBijective Y A).1
  have : Presheaf.IsLocallySurjective (ProEt.topology Y) (proEtaleModuleScalarUnit Y A) :=
    (proEtaleConstantRingUnit_locallyBijective Y A).2
  have := ConstantScalarComparison.constantComparisonHom_isIso (ProEt.topology Y)
    (ULift.{u + 1, u} A) R (proEtaleModuleScalarUnit Y A) M
  exact asIso (ConstantScalarComparison.constantComparisonHom (ProEt.topology Y)
    (ULift.{u + 1, u} A) R (proEtaleModuleScalarUnit Y A) M)

private noncomputable def sfbProEtale_pullback_constant
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A]
    (M : ModuleCat.{u + 1} A) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj
      ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj M) ≅
        (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M := by
  let D := ModuleCat.{u + 1} A
  exact (Functor.isoWhiskerLeft (constantSheaf (ProEt.topology Y) D)
    (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange f) D
      (ProEt.topology Y) (ProEt.topology X)).symm).app M ≪≫
    ((proEtaleBaseChange f).constantSheafsheafPullbackIso D
      (ProEt.topology Y) (ProEt.topology X) (ProEt.isTerminalMkId Y)
      ((ProEt.isTerminalMkId Y).isTerminalObj (proEtaleBaseChange f) _)).app M

private theorem sfbProEtale_models_encoding (Y : Scheme.{u})
    (A : Type u) [CommRing A]
    (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (projective : Bool) :
    sfbProEtaleFiniteLocalModels Y A H projective ↔
      ∃ C : Cover.{u + 1} proetalePrecoverage Y, ∀ j : C.I₀,
        ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A),
          (Finite M ∧ (projective = true → ∃ (n : ℕ)
            (i : M →ₗ[ULift.{u + 1, u} A] (Fin n → ULift.{u + 1, u} A))
            (r : (Fin n → ULift.{u + 1, u} A) →ₗ[ULift.{u + 1, u} A] M),
            r.comp i = LinearMap.id)) ∧
          Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            (C.f j)).obj ((proEtaleModuleRestriction Y A).obj H) ≅
              (constantSheaf (ProEt.topology (C.X j))
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj M) := by
  constructor
  · rintro ⟨I, U, f, hf, hm⟩
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 Y = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        proetalePrecoverage Y := by
      rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
      change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
        proetalePrecoverage Y at hf
      simpa only [hw] using hf
    let C : Cover.{u + 1} proetalePrecoverage Y :=
      ⟨⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom⟩, hg⟩
    refine ⟨C, fun i ↦ ?_⟩
    obtain ⟨M, hM, e, hp⟩ := hm i
    exact ⟨M, ⟨hM, hp⟩, (sfbProEtale_over_model_iff A H (U i) M).mp e⟩
  · rintro ⟨C, hm⟩
    have hg (i : C.I₀) : WeaklyEtale (C.f i) :=
      proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ ⟨i⟩
    let U (i : C.I₀) : Y.ProEt := @ProEt.mk Y (C.X i) (C.f i) (hg i)
    let f (i : C.I₀) : U i ⟶ ProEt.mk (𝟙 Y) :=
      MorphismProperty.Over.homMk (C.f i) (Category.comp_id _)
    refine ⟨C.I₀, U, f, ?_, fun i ↦ ?_⟩
    · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
      exact C.mem₀
    · obtain ⟨M, ⟨hM, hp⟩, e⟩ := hm i
      exact ⟨M, hM, (sfbProEtale_over_model_iff A H (U i) M).mpr e, hp⟩

private theorem sfbProEtale_fixed_models_invariance
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type (u + 1)) [CommRing A]
    (H : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))
    (P : ModuleCat.{u + 1} A → Prop) :
    (∃ C : Cover.{u + 1} proetalePrecoverage Y, ∀ j : C.I₀,
      ∃ M : ModuleCat.{u + 1} A, P M ∧
        Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} A) (C.f j)).obj H ≅
          (constantSheaf (ProEt.topology (C.X j)) (ModuleCat.{u + 1} A)).obj M)) ↔
    (∃ C : Cover.{u + 1} proetalePrecoverage T, ∀ j : C.I₀,
      ∃ M : ModuleCat.{u + 1} A, P M ∧
        Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} A) (C.f j)).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) h).obj H) ≅
            (constantSheaf (ProEt.topology (C.X j)) (ModuleCat.{u + 1} A)).obj M)) := by
  let D := ModuleCat.{u + 1} A
  let G := (ProEtale.upperStar D h).obj H
  constructor
  · rintro ⟨C, hc⟩
    refine ⟨C.pullback₂ h, fun j ↦ ?_⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hc j
    let p := Limits.pullback.fst (C.f j) h
    let q := Limits.pullback.snd (C.f j) h
    exact ⟨M, hM, ⟨((ProEtale.upperStarComp D q h).app H).symm ≪≫
      eqToIso (congrArg (fun f ↦ (ProEtale.upperStar D f).obj H)
        Limits.pullback.condition.symm) ≪≫
      (ProEtale.upperStarComp D p (C.f j)).app H ≪≫
      (ProEtale.upperStar D p).mapIso e ≪≫ sfbProEtale_pullback_constant p A M⟩⟩
  · rintro ⟨C, hc⟩
    have : Precoverage.Small.{u} proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (propQCPrecoverage @WeaklyEtale))
    let C' := Precoverage.ZeroHypercover.restrictIndexOfSmall.{u} C
    obtain ⟨B, hb⟩ := exists_cover_refinement_surjective_closed h C'
    refine ⟨B.reindex (Equiv.ulift : ULift.{u + 1, u} B.I₀ ≃ B.I₀), fun j ↦ ?_⟩
    obtain ⟨a, W, q, p, r, sq, hr⟩ := hb j.down
    obtain ⟨M, hM, ⟨e⟩⟩ := hc (Precoverage.ZeroHypercover.Small.restrictFun C a)
    have : IsClosedImmersion q := MorphismProperty.of_isPullback sq.flip inferInstance
    have : Surjective q := MorphismProperty.of_isPullback sq.flip inferInstance
    have : (ProEtale.upperStar D q).IsEquivalence :=
      ProEtale.isEquivalence_upperStar_of_isUniversalHomeomorphism D q
    let t : (ProEtale.upperStar D q).obj
        ((ProEtale.upperStar D (B.f j.down)).obj H) ≅
          (ProEtale.upperStar D r).obj
            ((ProEtale.upperStar D (C'.f a)).obj G) :=
      ((ProEtale.upperStarComp D q (B.f j.down)).app H).symm ≪≫
      eqToIso (congrArg (fun f ↦ (ProEtale.upperStar D f).obj H) sq.w) ≪≫
      (ProEtale.upperStarComp D p h).app H ≪≫
      eqToIso (congrArg (fun f ↦ (ProEtale.upperStar D f).obj G) hr.symm) ≪≫
      (ProEtale.upperStarComp D r (C'.f a)).app G
    exact ⟨M, hM, ⟨(ProEtale.upperStar D q).preimageIso
      (t ≪≫ (ProEtale.upperStar D r).mapIso e ≪≫
        sfbProEtale_pullback_constant r A M ≪≫
        (sfbProEtale_pullback_constant q A M).symm)⟩⟩

/-- Surjective closed restriction on the pro-etale site, for the published ordinary
constant-ring module operations and their tensor-unit-normalized adjunction.
Source: Stacks, Tag 09AB, Modules on Sites, lemma-adjoint-pullback-pushforward-modules
and lemma-pullback-locally-constant; blueprint det-sf-flat-model-generation, clause (2)
(blueprint: lem-sfb-surjective-closed-module-invariance).

Proof: restrict intrinsic constant-ring modules to their constant scalars, using
proEtaleModuleRestriction_isEquivalence. The direct-image comparison identifies
intrinsic pushforward, followed by restriction, with ModuleCat-valued pushforward.
The published pro-etale topological-invariance theorem makes the latter an
equivalence for a universal homeomorphism. Cancel the scalar restriction equivalence;
then the actual normalized adjunction makes pullback an equivalence too, with
invertible unit and counit.

The constant comparison for sheafified module presheaves identifies intrinsic
constant modules with ModuleCat-valued constant sheaves, including on localized
sites. The slice equivalence and upperStarIsoLocalizationRestriction translate
localized models into scheme-site inverse-image models. Constant-sheaf pullback
preserves each model, and the pullback-encoding comparison identifies the given
intrinsic pullback with fixed-module pullback.

Preservation pulls a trivializing cover back. Reflection uses the existing
surjective-closed-cover-refinement theorem, after shrinking the indexing universe.
For each refined member, the cartesian square gives a base-changed surjective
closed immersion q and a map r to an old cover member. Pull back its trivialization
along r, use composition comparisons and the square identity, and descend the
resulting constant-model isomorphism through the fully faithful inverse image q*.
The same argument works for any predicate on the models; specialize to finiteness
and the requested finite-free retractions. All models and splitting maps are reused.
Empty covers, empty schemes, the zero ring and rank zero require no exception. -/
theorem sfbProEtale_surjectiveClosed_module_invariance
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type u) [CommRing A] [Finite A] :
    IsIso (proEtaleConstantRingAdjunction A h).unit ∧
    IsIso (proEtaleConstantRingAdjunction A h).counit ∧
    (proEtaleConstantRingPullback A h).IsEquivalence ∧
    (proEtaleConstantRingPushforward A h).IsEquivalence ∧
    (∀ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A),
      Nonempty ((proEtaleConstantRingPullback A h).obj
        (proEtaleConstantModuleSheaf Y A M) ≅ proEtaleConstantModuleSheaf T A M)) ∧
    (∀ (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (projective : Bool),
      sfbProEtaleFiniteLocalModels Y A H projective ↔
        sfbProEtaleFiniteLocalModels T A
          ((proEtaleConstantRingPullback A h).obj H) projective) := by
  let D := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have : (proEtaleModuleRestriction Y A).IsEquivalence :=
    proEtaleModuleRestriction_isEquivalence Y A
  have : (proEtaleModuleRestriction T A).IsEquivalence :=
    proEtaleModuleRestriction_isEquivalence T A
  have : (ProEtale.lowerStar D h).IsEquivalence :=
    ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism D h
  have : (proEtaleConstantRingPushforward A h ⋙ proEtaleModuleRestriction Y A).IsEquivalence :=
    Functor.isEquivalence_of_iso (directImageComparison h A).symm
  have : (proEtaleConstantRingPushforward A h).IsEquivalence :=
    Functor.isEquivalence_of_comp_right _ (proEtaleModuleRestriction Y A)
  have : (proEtaleConstantRingPullback A h).IsEquivalence :=
    (proEtaleConstantRingAdjunction A h).isEquivalence_left_of_isEquivalence_right
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro M
    obtain ⟨e⟩ := proEtaleModuleRestriction_pullback_of_isIso h A
      (proEtaleConstantModuleSheaf Y A M)
    exact ⟨(proEtaleModuleRestriction T A).preimageIso
      (e ≪≫ (ProEtale.upperStar D h).mapIso
        (sfbProEtale_constant_comparison Y A M).symm ≪≫
        sfbProEtale_pullback_constant h _ M ≪≫ sfbProEtale_constant_comparison T A M)⟩
  · intro H projective
    let P := fun M : D ↦ Finite M ∧ (projective = true → ∃ (n : ℕ)
      (i : M →ₗ[ULift.{u + 1, u} A] (Fin n → ULift.{u + 1, u} A))
      (r : (Fin n → ULift.{u + 1, u} A) →ₗ[ULift.{u + 1, u} A] M),
      r.comp i = LinearMap.id)
    obtain ⟨e⟩ := proEtaleModuleRestriction_pullback_of_isIso h A H
    rw [sfbProEtale_models_encoding Y A H projective,
      sfbProEtale_models_encoding T A ((proEtaleConstantRingPullback A h).obj H) projective]
    constructor
    · intro hm
      obtain ⟨C, hc⟩ := (sfbProEtale_fixed_models_invariance h _
        ((proEtaleModuleRestriction Y A).obj H) P).mp hm
      refine ⟨C, fun j ↦ ?_⟩
      obtain ⟨M, hM, ⟨i⟩⟩ := hc j
      exact ⟨M, hM, ⟨(ProEtale.upperStar D (C.f j)).mapIso e ≪≫ i⟩⟩
    · rintro ⟨C, hc⟩
      apply (sfbProEtale_fixed_models_invariance h _
        ((proEtaleModuleRestriction Y A).obj H) P).mpr
      refine ⟨C, fun j ↦ ?_⟩
      obtain ⟨M, hM, ⟨i⟩⟩ := hc j
      exact ⟨M, hM, ⟨(ProEtale.upperStar D (C.f j)).mapIso e.symm ≪≫ i⟩⟩

end AlgebraicGeometry.Scheme
