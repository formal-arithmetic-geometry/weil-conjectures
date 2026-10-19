/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.Paper.ProEtaleModelTypePartition
import Sheaf.Paper.ProEtaleUniformModelEtaleCover
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.ProEtaleComparisonLocalization
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Finite-presentation local systems and the pro-etale twist

Source: Stacks Project, Tag 099Y, lemma-compare-locally-constant.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- A pro-etale local system with finitely presented constant models.
Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`
(blueprint: det-pe-finite-local-systems-twist). -/
def IsFinitePresentationProEtaleLocalSystem (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) : Prop :=
  Scheme.IsLocallyConstantProEtaleFixedModuleSheaf X (ULift.{u + 1, u} Λ) F ∧
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ Scheme.ProEt.mk (𝟙 X)),
      Presieve.ofArrows U f ∈ (Scheme.ProEt.precoverage X).coverings _ ∧
        ∀ i : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
          Module.FinitePresentation (ULift.{u + 1, u} Λ) M ∧
            Nonempty (F.over (U i) ≅
              (constantSheaf ((Scheme.ProEt.topology X).over (U i))
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M)

/-- An etale local system with finitely presented constant models.
Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`
(blueprint: det-pe-finite-local-systems-twist). -/
def IsFinitePresentationEtaleLocalSystem (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (G : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
      Module.FinitePresentation (ULift.{u + 1, u} Λ) M ∧
        Nonempty (G.over (𝒰.etalePrecoverageToEtale i) ≅
          (constantSheaf
            (X.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M)

/-- A pro-etale local system whose displayed constant models are finite as sets.
Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`; blueprint
`det-pe-finite-local-systems-twist`. -/
def IsFiniteModelProEtaleLocalSystem (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) : Prop :=
  Scheme.IsLocallyConstantProEtaleFixedModuleSheaf X (ULift.{u + 1, u} Λ) F ∧
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ Scheme.ProEt.mk (𝟙 X)),
      Presieve.ofArrows U f ∈ (Scheme.ProEt.precoverage X).coverings _ ∧
        ∀ i : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
          Finite M ∧
            Nonempty (F.over (U i) ≅
              (constantSheaf ((Scheme.ProEt.topology X).over (U i))
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M)

/-- An etale covering that trivializes a pro-etale sheaf after comparison.
Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`; blueprint
`det-pe-finite-local-systems-twist`. -/
def HasEtaleTrivializingCover (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
      Nonempty (F.over ((Scheme.toProEt X).obj (𝒰.etalePrecoverageToEtale i)) ≅
        (constantSheaf ((Scheme.ProEt.topology X).over
          ((Scheme.toProEt X).obj (𝒰.etalePrecoverageToEtale i)))
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M)

private noncomputable def constantComparisonIso
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) X ≅
        constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A) :=
  (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
      (Scheme.Etale.isTerminalMkId X)).comp
      (comparisonAdjunction (ModuleCat.{u + 1} A) X)).ofNatIsoRight
    ((toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso (ModuleCat.{u + 1} A)
      X.smallEtaleTopology (ProEt.topology X) (op (Scheme.Etale.mk (𝟙 X))))).leftAdjointUniq
    (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal _ _))

attribute [local instance] ProEt.sliceDense

private noncomputable def proEtaleSliceIso
    {X : Scheme.{u}} (A : Type (u + 1)) [CommRing A] (U : X.ProEt)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :
    ((ProEt.sliceEquiv X U).sheafCongr
      ((ProEt.topology X).over U) (ProEt.topology U.left)
      (ModuleCat.{u + 1} A)).functor.obj (F.over U) ≅
        (localizationRestriction (ModuleCat.{u + 1} A) U.hom U.prop).obj F :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))

private noncomputable def etaleLowerRestrictionIso
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (V : X.Etale) (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (AlgebraicGeometry.Etale.localizationRestriction
      (ModuleCat.{u + 1} A) V.hom V.prop).obj
      ((comparisonLowerStar (ModuleCat.{u + 1} A) X).obj F) ≅
    (comparisonLowerStar (ModuleCat.{u + 1} A) V.left).obj
      ((localizationRestriction (ModuleCat.{u + 1} A) V.hom inferInstance).obj F) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))

private noncomputable def emptySheafIso
    {X : Scheme.{u}} [IsEmpty X] (Λ : Type (u + 1)) [CommRing Λ]
    (F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) : F ≅ G := by
  have (T : X.ProEt) : IsEmpty T.left := ⟨fun t ↦ isEmptyElim (show X from T.hom t)⟩
  exact ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun T ↦ (ProEt.isTerminalSectionsOfIsEmpty F T.unop).uniqueUpToIso
      (ProEt.isTerminalSectionsOfIsEmpty G T.unop))
    (fun {_ _} _ ↦ (ProEt.isTerminalSectionsOfIsEmpty G _).hom_ext _ _))

private noncomputable def constantPullbackIso
    {X Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] (g : Y ⟶ X)
    [WeaklyEtale g] (M : ModuleCat.{u + 1} Λ) :
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).obj
      ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj M) ≅
        (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)).obj M :=
  (AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} Λ) g inferInstance).app _ ≪≫
    (Functor.pushforwardContinuousSheafificationCompatibility
      (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale g))
        (ModuleCat.{u + 1} Λ) (ProEt.topology Y) (ProEt.topology X)).symm.app
          ((Functor.const X.ProEtᵒᵖ).obj M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-presentation pro-etale local systems admit an etale cover with the same models.
Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
Use the fixed-coefficient model-type open loci. Base change the original cover to each
locus; overlap fibers identify every nonempty model with the chosen model. Empty
members have the unique module sheaf. Apply the finite-type uniform-model comparison
on that locus, then assemble the covers by choosing a locus above each point of X.
Composition preserves the displayed constant model and its finite presentation.
(blueprint: det-pe-finite-local-systems-etale-cover). -/
theorem etaleCover_of_finitelyPresentedModels
    (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))
    (hF : IsFinitePresentationProEtaleLocalSystem X Λ F) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
      ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
        Module.FinitePresentation (ULift.{u + 1, u} Λ) M ∧
          Nonempty ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) (𝒰.f i)).obj F ≅
            (constantSheaf (Scheme.ProEt.topology (𝒰.X i))
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M) := by
  classical
  obtain ⟨I, U, f, hf, hm⟩ := hF.2
  let W (i : I) := (U i).left
  let g (i : I) : W i ⟶ X := (U i).hom
  have hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈ _ at hf
    have he : (fun i ↦ (f i).left) = g := by
      funext i
      exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w (f i))
    rw [he] at hf
    exact hf
  have hmodels (i : I) : ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
      Module.FinitePresentation (ULift.{u + 1, u} Λ) M ∧
        Nonempty ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) (g i)).obj F ≅
          (constantSheaf (ProEt.topology (W i))
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M) := by
    obtain ⟨M, hM, ⟨e⟩⟩ := hm i
    let E := (ProEt.sliceEquiv X (U i)).sheafCongr
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
    let c := ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) Over.mkIdTerminal).app M
    exact ⟨M, hM, ⟨(upperStarIsoLocalizationRestriction _ (g i) (U i).prop).app F ≪≫
      (proEtaleSliceIso _ (U i) F).symm ≪≫ E.functor.mapIso e ≪≫ c⟩⟩
  choose M hM e using hmodels
  obtain ⟨O, hO, hcover⟩ := proEtale_model_type_opens (ULift.{u + 1, u} Λ) F W g hg M
    (fun i ↦ (e i).some)
  have (i : I) : WeaklyEtale (g i) :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ hg (.mk i)
  have huniform (i : I) : ∃ 𝒰 : Cover.{u} etalePrecoverage (O i).toScheme,
      ∀ a : 𝒰.I₀, Nonempty
        ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) (𝒰.f a)).obj
          ((AlgebraicGeometry.ProEtale.upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) (O i).ι).obj F) ≅
            (constantSheaf (ProEt.topology (𝒰.X a))
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj (M i)) := by
    have : Module.FinitePresentation (ULift.{u + 1, u} Λ) (M i) := hM i
    apply etale_cover_of_proetale_uniform_finiteType_model
      (O i).toScheme (ULift.{u + 1, u} Λ) _ (M i)
    refine ⟨I, (fun j ↦ pullback (g j) (O i).ι),
      (fun j ↦ pullback.snd (g j) (O i).ι), ?_, ?_⟩
    · exact Precoverage.mem_coverings_of_isPullback g hg (O i).ι _ _
        (fun j ↦ (IsPullback.of_hasPullback (g j) (O i).ι).flip)
    · intro j
      by_cases h : Nonempty (pullback (g j) (O i).ι : Scheme.{u})
      · obtain ⟨z⟩ := h
        have hz : g j ((pullback.fst (g j) (O i).ι) z) ∈ O i := by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
          exact (pullback.snd (g j) (O i).ι z).property
        obtain ⟨a⟩ := (hO i j _).1 hz
        let p := pullback.fst (g j) (O i).ι
        let q := pullback.snd (g j) (O i).ι
        let A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)
        exact ⟨((AlgebraicGeometry.ProEtale.upperStarComp A q (O i).ι).app F).symm ≪≫
          (eqToIso (congrArg (fun k ↦ (AlgebraicGeometry.ProEtale.upperStar A k).obj F)
            (pullback.condition (f := g j) (g := (O i).ι)).symm)) ≪≫
          (AlgebraicGeometry.ProEtale.upperStarComp A p (g j)).app F ≪≫
          (AlgebraicGeometry.ProEtale.upperStar A p).mapIso (e j).some ≪≫
          constantPullbackIso (ULift.{u + 1, u} Λ) p (M j) ≪≫
          (constantSheaf (ProEt.topology (pullback (g j) (O i).ι)) A).mapIso a⟩
      · have : IsEmpty (pullback (g j) (O i).ι : Scheme.{u}) := not_nonempty_iff.mp h
        exact ⟨emptySheafIso (ULift.{u + 1, u} Λ) _ _⟩
  choose 𝒰 h𝒰 using huniform
  have hpoint (x : X) : ∃ i, x ∈ O i := by
    have hx : x ∈ ⋃ i, (O i : Set X) := by rw [hcover]; trivial
    exact Set.mem_iUnion.mp hx
  choose index hindex using hpoint
  let P (a : Σ x : X, (𝒰 (index x)).I₀) : Scheme.{u} := (𝒰 (index a.1)).X a.2
  let f (a : Σ x : X, (𝒰 (index x)).I₀) : P a ⟶ X :=
    (𝒰 (index a.1)).f a.2 ≫ (O (index a.1)).ι
  have (a : Σ x : X, (𝒰 (index x)).I₀) : Etale (f a) := by
    dsimp [f]
    infer_instance
  have hf : ∀ x : X, ∃ a, ∃ y : P a, f a y = x := by
    intro x
    let y : (O (index x)).toScheme := ⟨x, hindex x⟩
    obtain ⟨a, z, hz⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1
      (𝒰 (index x)).mem₀).1 y
    refine ⟨⟨x, a⟩, z, ?_⟩
    change ((𝒰 (index x)).f a ≫ (O (index x)).ι) z = x
    rw [Scheme.Hom.comp_apply, hz]
    rfl
  let 𝒱 : Cover.{u} etalePrecoverage X :=
    Cover.mkOfCovers (Σ x : X, (𝒰 (index x)).I₀) P f
      (fun x ↦ by obtain ⟨a, y, hy⟩ := hf x; exact ⟨a, y, hy⟩)
      inferInstance
  refine ⟨𝒱, ?_⟩
  rintro ⟨x, a⟩
  exact ⟨M (index x), hM (index x),
    ⟨(AlgebraicGeometry.ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
      ((𝒰 (index x)).f a) (O (index x)).ι).app F ≪≫ (h𝒰 (index x) a).some⟩⟩

private theorem lowerLocalSystem (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))
    (hF : IsFinitePresentationProEtaleLocalSystem X Λ F) :
    IsFinitePresentationEtaleLocalSystem X Λ
      ((comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X).obj F) ∧
    HasEtaleTrivializingCover X Λ F ∧
    IsIso ((comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X).counit.app F) := by
  classical
  obtain ⟨𝒰, hmodels⟩ := etaleCover_of_finitelyPresentedModels X Λ F hF
  let A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)
  let G := (comparisonLowerStar A X).obj F
  have hG : IsFinitePresentationEtaleLocalSystem X Λ G := by
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hmodels i
    let V := 𝒰.etalePrecoverageToEtale i
    let E := (Scheme.Etale.overSheafEquiv V A).functor
    let R := comparisonLowerStar A V.left
    let T := (constantSheaf V.left.smallEtaleTopology A).obj M
    let eF : (localizationRestriction A V.hom inferInstance).obj F ≅
        (constantSheaf (ProEt.topology V.left) A).obj M :=
      ((upperStarIsoLocalizationRestriction A V.hom inferInstance).app F).symm ≪≫ e
    have : IsIso (comparisonAdjunction A V.left).unit :=
      isIso_comparisonAdjunction_unit A V.left
    let eG : E.obj (G.over V) ≅ T :=
      overSheafEquivFunctorObjOverIso A V G ≪≫
      (AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction A V.hom V.prop).app G ≪≫
      etaleLowerRestrictionIso X _ V F ≪≫ R.mapIso eF ≪≫
      R.mapIso ((constantComparisonIso V.left _).app M).symm ≪≫
      (asIso ((comparisonAdjunction A V.left).unit.app T)).symm
    let c := ((Scheme.Etale.overEquiv V).constantSheafSheafCongrIso
      (X.smallEtaleTopology.over V) V.left.smallEtaleTopology A Over.mkIdTerminal).app M
    exact ⟨M, hM, ⟨E.preimageIso (eG ≪≫ c.symm)⟩⟩
  have hcover : HasEtaleTrivializingCover X Λ F := by
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨M, _, ⟨e⟩⟩ := hmodels i
    let U := (toProEt X).obj (𝒰.etalePrecoverageToEtale i)
    let E := (ProEt.sliceEquiv X U).sheafCongr
      ((ProEt.topology X).over U) (ProEt.topology U.left) A
    let c := ((ProEt.sliceEquiv X U).constantSheafSheafCongrIso
      ((ProEt.topology X).over U) (ProEt.topology U.left) A Over.mkIdTerminal).app M
    exact ⟨M, ⟨E.functor.preimageIso (proEtaleSliceIso _ U F ≪≫
      ((upperStarIsoLocalizationRestriction A U.hom U.prop).app F).symm ≪≫ e ≪≫ c.symm)⟩⟩
  have hcounit : IsIso ((comparisonAdjunction A X).counit.app F) := by
    have : ∀ i, WeaklyEtale (𝒰.f i) := fun i ↦ inferInstance
    apply isIso_of_isIso_localizationRestriction A
      ((comparisonAdjunction A X).counit.app F) 𝒰.f
      (etalePrecoverage_le_proetalePrecoverage _ 𝒰.mem₀)
    intro i
    obtain ⟨M, _, ⟨e⟩⟩ := hmodels i
    let V := 𝒰.etalePrecoverageToEtale i
    let eF : (localizationRestriction A V.hom inferInstance).obj F ≅
        (comparisonUpperStar A V.left).obj
          ((constantSheaf V.left.smallEtaleTopology A).obj M) :=
      ((upperStarIsoLocalizationRestriction A V.hom inferInstance).app F).symm ≪≫ e ≪≫
        ((constantComparisonIso V.left _).app M).symm
    exact comparison_counit_restriction_isIso X _ V F
      ((comparisonAdjunction A V.left).isIso_counit_app_of_iso eF)
  exact ⟨hG, hcover, hcounit⟩

private theorem upperLocalSystem (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))
    (hG : IsFinitePresentationEtaleLocalSystem X Λ G) :
    IsFinitePresentationProEtaleLocalSystem X Λ
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X).obj G) := by
  classical
  obtain ⟨𝒰, hmodels⟩ := hG
  let A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)
  let F := (comparisonUpperStar A X).obj G
  let U (i : ULift.{u + 1} 𝒰.I₀) : X.ProEt :=
    (toProEt X).obj (𝒰.etalePrecoverageToEtale i.down)
  let f (i : ULift.{u + 1} 𝒰.I₀) : U i ⟶ ProEt.mk (𝟙 X) :=
    MorphismProperty.Over.homMk (𝒰.f i.down) (by
      change 𝒰.f i.down ≫ 𝟙 X = 𝒰.f i.down
      exact Category.comp_id _)
  have hf : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    have heq : Presieve.ofArrows
        (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.X i.down)
        (fun i ↦ 𝒰.f i.down) = 𝒰.presieve₀ := by
      refine le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩) fun _ _ ⟨i⟩ ↦ ?_
      exact Presieve.ofArrows.mk (ι := ULift.{u + 1} 𝒰.I₀) (Y := fun i ↦ 𝒰.X i.down) ⟨i⟩
    change Presieve.ofArrows (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.X i.down)
      (fun i ↦ 𝒰.f i.down) ∈ _
    rw [heq]
    exact etalePrecoverage_le_proetalePrecoverage _ 𝒰.mem₀
  have hm (i : ULift.{u + 1} 𝒰.I₀) : ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
      Module.FinitePresentation (ULift.{u + 1, u} Λ) M ∧
        Nonempty (F.over (U i) ≅
          (constantSheaf ((ProEt.topology X).over (U i)) A).obj M) := by
    obtain ⟨M, hM, ⟨e⟩⟩ := hmodels i.down
    let V := 𝒰.etalePrecoverageToEtale i.down
    let E := (Scheme.Etale.overSheafEquiv V A).functor
    let eG : (AlgebraicGeometry.Etale.upperStar A V.hom).obj G ≅
        (constantSheaf V.left.smallEtaleTopology A).obj M :=
      (overSheafEquivFunctorObjOverIso A V G).symm ≪≫ E.mapIso e ≪≫
        ((Scheme.Etale.overEquiv V).constantSheafSheafCongrIso
          (X.smallEtaleTopology.over V) V.left.smallEtaleTopology A Over.mkIdTerminal).app M
    let eF : (upperStar A V.hom).obj F ≅
        (constantSheaf (ProEt.topology V.left) A).obj M :=
      (comparisonUpperStarCompUpperStarIso A V.hom).app G ≪≫
        (comparisonUpperStar A V.left).mapIso eG ≪≫ (constantComparisonIso V.left _).app M
    let E' := (ProEt.sliceEquiv X (U i)).sheafCongr
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left) A
    let c := ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left) A Over.mkIdTerminal).app M
    exact ⟨M, hM, ⟨E'.functor.preimageIso (proEtaleSliceIso _ (U i) F ≪≫
      ((upperStarIsoLocalizationRestriction A V.hom inferInstance).app F).symm ≪≫
      eF ≪≫ c.symm)⟩⟩
  exact ⟨⟨_, U, f, hf, fun i ↦ by obtain ⟨M, _, he⟩ := hm i; exact ⟨M, he⟩⟩,
    ⟨_, U, f, hf, hm⟩⟩

/-- Finite-presentation pro-etale local systems come from etale local systems.
Source: Stacks Project, Tag 099Y, lemma-compare-locally-constant.
First obtain an etale cover with the original finitely presented models. The comparison
lower star is locally constant on this cover, by constant comparison and the invertible
comparison unit. The counit is invertible after restricting to each cover member;
local conservativity makes it invertible globally, giving the etale origin and
classicality. Slice localization gives the asserted trivializing cover. The reverse
preservation follows by applying comparison to each etale constant model. Full
faithfulness and the unit are the existing comparison theorems; the counit is the one
just constructed. Over a finite ring every finite module is finitely presented by
Noetherianity. No hypothesis on the scheme or the coefficient ring is added.
(blueprint: det-pe-finite-local-systems-twist). -/
theorem finiteLocalSystemsTwist (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) :
    IsFinitePresentationProEtaleLocalSystem X Λ F →
      (∃ G : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationEtaleLocalSystem X Λ G ∧
          Nonempty ((comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1, u} Λ)) X).obj G ≅ F)) ∧
      IsClassical ((sheafCompose (Scheme.ProEt.topology X)
        (forget (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))).obj F) ∧
      HasEtaleTrivializingCover X Λ F ∧
      (∀ G : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationEtaleLocalSystem X Λ G →
          IsFinitePresentationProEtaleLocalSystem X Λ
            ((comparisonUpperStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} Λ)) X).obj G)) ∧
      (∀ F' : Sheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationProEtaleLocalSystem X Λ F' →
          IsFinitePresentationEtaleLocalSystem X Λ
            ((comparisonLowerStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} Λ)) X).obj F')) ∧
      (∀ G H : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationEtaleLocalSystem X Λ G →
          IsFinitePresentationEtaleLocalSystem X Λ H →
          Function.Bijective (fun φ : G ⟶ H ↦
            (comparisonUpperStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} Λ)) X).map φ)) ∧
      (∀ G : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationEtaleLocalSystem X Λ G →
          IsIso ((comparisonAdjunction (ModuleCat.{u + 1}
            (ULift.{u + 1, u} Λ)) X).unit.app G)) ∧
      (∀ F' : Sheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationProEtaleLocalSystem X Λ F' →
          IsIso ((comparisonAdjunction (ModuleCat.{u + 1}
            (ULift.{u + 1, u} Λ)) X).counit.app F')) ∧
      (Finite Λ →
        ∀ F' : Sheaf (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
          IsFiniteModelProEtaleLocalSystem X Λ F' →
            IsFinitePresentationProEtaleLocalSystem X Λ F')  := by
  intro hF
  let A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)
  obtain ⟨hG, hcover, hcounit⟩ := lowerLocalSystem X Λ F hF
  have : IsIso ((comparisonAdjunction A X).counit.app F) := hcounit
  have horigin : ∃ G : Sheaf X.smallEtaleTopology A,
      Nonempty ((comparisonUpperStar A X).obj G ≅ F) :=
    ⟨(comparisonLowerStar A X).obj F, ⟨asIso ((comparisonAdjunction A X).counit.app F)⟩⟩
  obtain ⟨_, _, _, _, _, hclassical⟩ := proEtaleClassicalSheavesModules X
    (ULift.{u + 1, u} Λ)
  refine ⟨⟨(comparisonLowerStar A X).obj F, hG,
      ⟨asIso ((comparisonAdjunction A X).counit.app F)⟩⟩,
    (hclassical F).mpr horigin, hcover, upperLocalSystem X Λ, ?_, ?_, ?_, ?_, ?_⟩
  · intro F' hF'
    exact (lowerLocalSystem X Λ F' hF').1
  · intro G H _ _
    exact (Functor.FullyFaithful.ofFullyFaithful (comparisonUpperStar A X)).map_bijective G H
  · intro G _
    have : IsIso (comparisonAdjunction A X).unit := isIso_comparisonAdjunction_unit A X
    infer_instance
  · intro F' hF'
    exact (lowerLocalSystem X Λ F' hF').2.2
  · intro hΛ F' hF'
    have : Finite Λ := hΛ
    obtain ⟨hlocal, I, U, f, hf, hmodels⟩ := hF'
    refine ⟨hlocal, I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, hM, he⟩ := hmodels i
    have : Finite M := hM
    exact ⟨M, Module.finitePresentation_of_finite (ULift.{u + 1, u} Λ) M, he⟩

end AlgebraicGeometry.ProEtale

