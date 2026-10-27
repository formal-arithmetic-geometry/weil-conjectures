/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups P2 and W4
-/
module

public import Sheaf.Paper.SupportedImageBoundedDerivedGeneration
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import Sheaf.Paper.FiniteConstructibleComplexHeartPresentations
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import all Sheaf.Paper.QcqsConstructibleIntegralLatticeTree
import all Sheaf.Paper.PadicAlgClConstructibleScalarRestriction
import Sheaf.Paper.PullbackFiniteConstantLocalModel
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Sheaf.Paper.FiniteCoefficientSerreIndHeart
import Sheaf.Paper.NoetherianFiniteComplexHeartFilteredClosure
import Sheaf.Paper.SupportedModelHullComparison
import Sheaf.Paper.SupportedModelHullProetaleDescent

/-! # Supported derived generation of the constructible weak Serre heart

Source: coefficient-generation step of the agent-formulated obligation in
blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph.
(blueprint: lem-sfb-weak-serre-supported-derived-generation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w d

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar upperStarFromPoint
  DerivedCategory.singleFunctors CochainComplex.singleFunctors
  HomotopyCategory.singleFunctors upperStarComp upperStarId HasDerivedCategory.standard

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem single_inverse_filtered
    (X : Scheme.{u})
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsSupportedImageGenerationClass Λ X P)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    (P.inverseImage (DerivedCategory.singleFunctor _ 0)).IsClosedUnderColimitsOfShape I := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let T := CochainComplex.singleFunctor A 0
  have : PreservesColimitsOfShape I T :=
    inferInstanceAs (PreservesColimitsOfShape I (HomologicalComplex.single A (.up ℤ) 0))
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  constructor
  rintro M ⟨pres⟩
  let D := pres.diag
  let c := pres.cocone
  have hc := pres.isColimit
  have hD := pres.prop_diag_obj
  apply P.prop_of_iso ((DerivedCategory.singleFunctorIsoCompQ A 0).app M).symm
  apply hP.2.2.2.2.2 I (D ⋙ T) 0 (T.mapCocone c) (isColimitOfPreserves T hc)
  · intro i
    dsimp only [Functor.comp_obj, T]
    infer_instance
  · intro i
    exact P.prop_of_iso ((DerivedCategory.singleFunctorIsoCompQ A 0).app (D.obj i)) (hD i)

private theorem single_inverse_extensions
    (X : Scheme.{u})
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsSupportedImageGenerationClass Λ X P) :
    (P.inverseImage (DerivedCategory.singleFunctor _ 0)).IsClosedUnderExtensions := by
  have : P.IsTriangulated := hP.1
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  constructor
  intro S hs h₁ h₃
  exact P.ext_of_isTriangulatedClosed₂ _ hs.singleTriangle_distinguished h₁ h₃

private theorem single_inverse_coproducts
    (X : Scheme.{u})
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsSupportedImageGenerationClass Λ X P)
    (I : Type (u + 1)) :
    (P.inverseImage (DerivedCategory.singleFunctor _ 0)).IsClosedUnderColimitsOfShape
      (Discrete I) := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let H := P.inverseImage (DerivedCategory.singleFunctor A 0)
  have : P.IsTriangulated := hP.1
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  have : H.IsClosedUnderIsomorphisms := inferInstance
  have : H.ContainsZero := by
    refine ⟨0, isZero_zero A, ?_⟩
    exact P.prop_of_isZero ((DerivedCategory.singleFunctor A 0).map_isZero (isZero_zero A))
  have : H.IsClosedUnderExtensions := single_inverse_extensions Λ X P hP
  have : H.IsClosedUnderBinaryCoproducts := .mk' (by
    rintro _ ⟨F, hF⟩
    exact H.prop_of_iso
      (biprod.isoCoprod _ _ ≪≫ (HasColimit.isoOfNatIso (diagramIsoPair F)).symm)
      (H.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))
  have : H.IsClosedUnderFiniteCoproducts := .mk'
  have : H.IsClosedUnderColimitsOfShape (Finset (Discrete I)) :=
    single_inverse_filtered Λ X P hP _
  have : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  constructor
  rintro N ⟨pres⟩
  let F := pres.diag
  let B : I → A := fun i ↦ F.obj ⟨i⟩
  have hB : ∀ i, H (B i) := fun i ↦ pres.prop_diag_obj ⟨i⟩
  have hc : H (∐ B) := by
    apply H.prop_of_isColimit
      (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone B)
    intro t
    exact H.prop_coproduct (fun s : t ↦ hB s.val.as)
  let e : Discrete.functor B ≅ F := Discrete.natIso (fun i ↦ Iso.refl (F.obj i))
  exact H.prop_of_iso (HasColimit.isoOfNatIso e ≪≫
    (colimit.isColimit F).coconePointUniqueUpToIso pres.isColimit) hc

private theorem finite_model_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun a ↦ ?_⟩
  obtain ⟨L, hL, ⟨eL⟩⟩ := hU a
  exact ⟨L, hL, ⟨(upperStar Λ (U.f a)).mapIso e.symm ≪≫ eL⟩⟩

private theorem finite_model_zero {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

private def treeModels : {X : Scheme.{u}} →
    (t : QcqsOpenClosedTree X) →
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) → Prop
  | _, @QcqsOpenClosedTree.leaf X _ _, M => HasFiniteConstantLocalModel Λ X M
  | _, @QcqsOpenClosedTree.split _ _ _ _ _ j i _ _ _ _ _ a b, M =>
      treeModels a ((upperStar Λ j).obj M) ∧ treeModels b ((upperStar Λ i).obj M)

private theorem tree_models_iso {X : Scheme.{u}} (t : QcqsOpenClosedTree X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : treeModels Λ t M) : treeModels Λ t N := by
  induction t with
  | leaf X => exact finite_model_iso Λ e hM
  | split j i hc a b iha ihb =>
    exact ⟨iha ((upperStar Λ j).mapIso e) hM.1,
      ihb ((upperStar Λ i).mapIso e) hM.2⟩

private theorem tree_models_generation
    {Y : Scheme.{u}}
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    {X : Scheme.{u}} (tree : QcqsOpenClosedTree X)
    (J : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (hgen : ∀ (S : Scheme.{u}) (p : tree.Path S)
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
      HasFiniteConstantLocalModel Λ S L →
        P ((DerivedCategory.singleFunctor _ 0).obj (J.obj ((p.extension Λ).obj L))))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : treeModels Λ tree M) :
    P ((DerivedCategory.singleFunctor _ 0).obj (J.obj M)) := by
  induction tree generalizing Y with
  | leaf X => exact hgen X (.root _) M hM
  | @split X U Z hX hqs j i hj hi hjqc hiqc hc a b iha ihb =>
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by rw [hc, compl_compl]
    have := closedSupport_lowerStarExact Λ i j hij
    obtain ⟨S, hs, hs₂, hs₁, hs₃⟩ :=
      AlgebraicGeometry.ProEtale.localization_shortExact Λ j i hc M
    have h₁ : P ((DerivedCategory.singleFunctor _ 0).obj (J.obj S.X₁)) := by
      rw [hs₁]
      exact iha P ((openImmersionLowerShriek Λ j) ⋙ J)
        (fun W p L hL ↦ hgen W (.openBranch j i hc a b p) L hL)
        ((upperStar Λ j).obj M) hM.1
    have h₃ : P ((DerivedCategory.singleFunctor _ 0).obj (J.obj S.X₃)) := by
      rw [hs₃]
      exact ihb P ((lowerStar Λ i) ⋙ J)
        (fun W p L hL ↦ hgen W (.closedBranch j i hc a b p) L hL)
        ((upperStar Λ i).obj M) hM.2
    have hm := P.ext_of_isTriangulatedClosed₂ (hs.map_of_exact J).singleTriangle
      (hs.map_of_exact J).singleTriangle_distinguished h₁ h₃
    change P ((DerivedCategory.singleFunctor _ 0).obj (J.obj S.X₂)) at hm
    simpa only [hs₂] using hm

private theorem tree_image_generation
    {Y : Scheme.{u}}
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    {X : Scheme.{u}} (tree : QcqsOpenClosedTree X)
    (J : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (hgen : ∀ (S : Scheme.{u}) (p : tree.Path S)
      (L N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
      (f : L ⟶ N), HasFiniteConstantLocalModel Λ S L →
      HasFiniteConstantLocalModel Λ S N →
        P ((DerivedCategory.singleFunctor _ 0).obj
          (J.obj ((p.extension Λ).obj (image f)))))
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : M ⟶ N) (hM : treeModels Λ tree M) (hN : treeModels Λ tree N) :
    P ((DerivedCategory.singleFunctor _ 0).obj (J.obj (image f))) := by
  induction tree generalizing Y with
  | leaf X => exact hgen X (.root _) M N f hM hN
  | @split X U Z hX hqs j i hj hi hjqc hiqc hc a b iha ihb =>
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by rw [hc, compl_compl]
    have := closedSupport_lowerStarExact Λ i j hij
    obtain ⟨S, hs, hs₂, hs₁, hs₃⟩ :=
      AlgebraicGeometry.ProEtale.localization_shortExact Λ j i hc (image f)
    have h₁ : P ((DerivedCategory.singleFunctor _ 0).obj (J.obj S.X₁)) := by
      rw [hs₁]
      let F := upperStar Λ j
      let G := openImmersionLowerShriek Λ j ⋙ J
      have hm := iha P G
        (fun W p L N f hL hN ↦ hgen W (.openBranch j i hc a b p) L N f hL hN)
        (F.obj M) (F.obj N) (F.map f) hM.1 hN.1
      exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
        (G.mapIso (PreservesImage.iso F f))) hm
    have h₃ : P ((DerivedCategory.singleFunctor _ 0).obj (J.obj S.X₃)) := by
      rw [hs₃]
      let F := upperStar Λ i
      let G := lowerStar Λ i ⋙ J
      have hm := ihb P G
        (fun W p L N f hL hN ↦ hgen W (.closedBranch j i hc a b p) L N f hL hN)
        (F.obj M) (F.obj N) (F.map f) hM.2 hN.2
      exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
        (G.mapIso (PreservesImage.iso F f))) hm
    have hm := P.ext_of_isTriangulatedClosed₂ (hs.map_of_exact J).singleTriangle
      (hs.map_of_exact J).singleTriangle_distinguished h₁ h₃
    change P ((DerivedCategory.singleFunctor _ 0).obj (J.obj S.X₂)) at hm
    simpa only [hs₂] using hm

private theorem refinement_models
    {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {T : Scheme.{u}} {t : T ⟶ X}
    (tr : LatticeRefinementTree X T t)
    (htr : tr.AllLeaves (fun W w ↦ IsEmpty W ∨
      HasFiniteConstantLocalModel Λ W ((upperStar Λ w).obj M))) :
    ∃ tree : QcqsOpenClosedTree T,
      treeModels Λ tree ((upperStar Λ t).obj M) := by
  induction tr with
  | @tip T t hcompact hqs himm =>
    let := hcompact
    let := hqs
    refine ⟨.leaf T, ?_⟩
    rcases htr with he | hm
    · let := he
      exact finite_model_zero Λ _ (AlgebraicGeometry.ProEtale.lattice_module_empty Λ _)
    · exact hm
  | @node T U Z t j i hcompact hqs himm hj hi hjqc hiqc hcover hd ha
      left right ihl ihr =>
    let := hcompact
    let := hqs
    let := hj
    let := hi
    let := hjqc
    let := hiqc
    obtain ⟨a, ha⟩ := ihl htr.1
    obtain ⟨b, hb⟩ := ihr htr.2
    have hc : Set.range j.base = (Set.range i.base)ᶜ :=
      eq_compl_iff_isCompl.mpr ⟨hd, codisjoint_iff.mpr hcover⟩
    exact ⟨.split j i hc a b,
      tree_models_iso Λ a ((upperStarComp Λ j t).app M) ha,
      tree_models_iso Λ b ((upperStarComp Λ i t).app M) hb⟩

private theorem refinement_pair_models
    {X : Scheme.{u}}
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {T : Scheme.{u}} {t : T ⟶ X}
    (tr : LatticeRefinementTree X T t)
    (htr : tr.AllLeaves (fun W w ↦ IsEmpty W ∨
      (HasFiniteConstantLocalModel Λ W ((upperStar Λ w).obj M) ∧
        HasFiniteConstantLocalModel Λ W ((upperStar Λ w).obj N)))) :
    ∃ tree : QcqsOpenClosedTree T,
      treeModels Λ tree ((upperStar Λ t).obj M) ∧
        treeModels Λ tree ((upperStar Λ t).obj N) := by
  induction tr with
  | @tip T t hcompact hqs himm =>
    let := hcompact
    let := hqs
    refine ⟨.leaf T, ?_⟩
    rcases htr with he | hm
    · let := he
      exact ⟨finite_model_zero Λ _ (AlgebraicGeometry.ProEtale.lattice_module_empty Λ _),
        finite_model_zero Λ _ (AlgebraicGeometry.ProEtale.lattice_module_empty Λ _)⟩
    · exact hm
  | @node T U Z t j i hcompact hqs himm hj hi hjqc hiqc hcover hd ha
      left right ihl ihr =>
    let := hcompact
    let := hqs
    let := hj
    let := hi
    let := hjqc
    let := hiqc
    obtain ⟨a, ha⟩ := ihl htr.1
    obtain ⟨b, hb⟩ := ihr htr.2
    have hc : Set.range j.base = (Set.range i.base)ᶜ :=
      eq_compl_iff_isCompl.mpr ⟨hd, codisjoint_iff.mpr hcover⟩
    exact ⟨.split j i hc a b,
      ⟨tree_models_iso Λ a ((upperStarComp Λ j t).app M) ha.1,
        tree_models_iso Λ b ((upperStarComp Λ i t).app M) hb.1⟩,
      ⟨tree_models_iso Λ a ((upperStarComp Λ j t).app N) ha.2,
        tree_models_iso Λ b ((upperStarComp Λ i t).app N) hb.2⟩⟩

private theorem constructible_generation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M)
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsSupportedImageGenerationClass Λ X P) :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  classical
  have : P.IsTriangulated := hP.1
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  obtain ⟨S, hS⟩ := (by simpa only [IsConstantModelConstructible, if_pos hX] using hM :
    IsFiniteConstantStratified Λ X M)
  obtain ⟨tr, htr⟩ := AlgebraicGeometry.ProEtale.lattice_refinement S
  have ht : tr.AllLeaves (fun T t ↦ IsEmpty T ∨
      HasFiniteConstantLocalModel Λ T ((upperStar Λ t).obj M)) := by
    apply tr.allLeaves_mono _ htr
    intro T t ht
    by_cases hn : Nonempty T
    · right
      obtain ⟨a, f, hf⟩ := ht hn
      have hm := pullback_finiteConstantLocalModel Λ f _ (hS a)
      apply finite_model_iso Λ ((upperStarComp Λ f (S.immersion a)).app M).symm at hm
      exact finite_model_iso Λ (eqToIso (congrArg
        (fun r ↦ (upperStar Λ r).obj M) hf)) hm
    · exact Or.inl (not_nonempty_iff.mp hn)
  obtain ⟨tree, ht⟩ := refinement_models Λ M tr ht
  have hm := tree_models_generation Λ P tree (𝟭 _)
    (fun T p L hL ↦ hP.2.2.2.2.1 tree T p L hL)
    ((upperStar Λ (𝟙 X)).obj M) ht
  exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
    ((upperStarId Λ X).app M)) hm

private theorem finite_model_comp
    {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ Y ((upperStar Λ g).obj M)) :
    HasFiniteConstantLocalModel Λ Z ((upperStar Λ (f ≫ g)).obj M) := by
  exact finite_model_iso Λ ((upperStarComp Λ f g).app M).symm
    (pullback_finiteConstantLocalModel Λ f _ hM)

private theorem inter_factors
    {X : Scheme.{u}} (S T : Scheme.Stratification X) (a : Fin (S.inter T).n) :
    ∃ (i : Fin S.n) (j : Fin T.n)
      (f : (S.inter T).domain a ⟶ S.domain i)
      (g : (S.inter T).domain a ⟶ T.domain j),
      f ≫ S.immersion i = (S.inter T).immersion a ∧
      g ≫ T.immersion j = (S.inter T).immersion a := by
  refine ⟨(finProdFinEquiv.symm a).1, (finProdFinEquiv.symm a).2,
    pullback.fst _ _, pullback.snd _ _, rfl, ?_⟩
  exact (pullback.condition).symm

attribute [local irreducible] Scheme.Stratification.inter

private theorem inter_models
    {X : Scheme.{u}} (S T : Scheme.Stratification X)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hS : ∀ a, HasFiniteConstantLocalModel Λ (S.domain a)
      ((upperStar Λ (S.immersion a)).obj M))
    (hT : ∀ a, HasFiniteConstantLocalModel Λ (T.domain a)
      ((upperStar Λ (T.immersion a)).obj N)) :
    ∀ a, HasFiniteConstantLocalModel Λ ((S.inter T).domain a)
      ((upperStar Λ ((S.inter T).immersion a)).obj M) ∧
      HasFiniteConstantLocalModel Λ ((S.inter T).domain a)
        ((upperStar Λ ((S.inter T).immersion a)).obj N) := by
  intro a
  obtain ⟨i, j, f, g, hf, hg⟩ := inter_factors S T a
  constructor
  · simpa only [hf] using finite_model_comp Λ f (S.immersion i) M (hS i)
  · simpa only [hg] using finite_model_comp Λ g (T.immersion j) N (hT j)

private theorem constructible_image_generation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsSupportedImageGenerationClass Λ X P)
    (himage : ∀ (tree : QcqsOpenClosedTree X) (S : Scheme.{u}) (p : tree.Path S)
      (L N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
      (f : L ⟶ N), HasFiniteConstantLocalModel Λ S L →
      HasFiniteConstantLocalModel Λ S N →
        P ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj (image f))))
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : M ⟶ N) (hM : IsConstantModelConstructible Λ X M)
    (hN : IsConstantModelConstructible Λ X N) :
    P ((DerivedCategory.singleFunctor _ 0).obj (image f)) := by
  classical
  have : P.IsTriangulated := hP.1
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  obtain ⟨S, hS⟩ := (by simpa only [IsConstantModelConstructible, if_pos hX] using hM :
    IsFiniteConstantStratified Λ X M)
  obtain ⟨T, hT⟩ := (by simpa only [IsConstantModelConstructible, if_pos hX] using hN :
    IsFiniteConstantStratified Λ X N)
  obtain ⟨V, hV⟩ : ∃ V : AlgebraicGeometry.Scheme.Stratification X, ∀ a : Fin V.n,
      HasFiniteConstantLocalModel Λ (V.domain a) ((upperStar Λ (V.immersion a)).obj M) ∧
      HasFiniteConstantLocalModel Λ (V.domain a) ((upperStar Λ (V.immersion a)).obj N) := by
    exact ⟨S.inter T, inter_models Λ S T M N hS hT⟩
  obtain ⟨tr, htr⟩ := AlgebraicGeometry.ProEtale.lattice_refinement V
  have ht : tr.AllLeaves (fun W w ↦ IsEmpty W ∨
      (HasFiniteConstantLocalModel Λ W ((upperStar Λ w).obj M) ∧
        HasFiniteConstantLocalModel Λ W ((upperStar Λ w).obj N))) := by
    apply tr.allLeaves_mono _ htr
    intro W w hw
    by_cases hn : Nonempty W
    · right
      obtain ⟨a, g, hg⟩ := hw hn
      constructor
      · simpa only [hg] using finite_model_comp Λ g (V.immersion a) M (hV a).1
      · simpa only [hg] using finite_model_comp Λ g (V.immersion a) N (hV a).2
    · exact Or.inl (not_nonempty_iff.mp hn)
  obtain ⟨tree, hm, hn⟩ := refinement_pair_models Λ M N tr ht
  let F := upperStar Λ (𝟙 X)
  have hi := tree_image_generation Λ P tree (𝟭 _)
    (fun W p L N f hL hN ↦ himage tree W p L N f hL hN)
    (F.obj M) (F.obj N) (F.map f) hm hn
  apply P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
    (PreservesImage.iso F f ≪≫ (upperStarId Λ X).app (image f)))
  exact hi

private theorem single_relations_of_image
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{d} A]
    (P : ObjectProperty (DerivedCategory A))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    {M N : A}
    (f : M ⟶ N)
    (hM : P ((DerivedCategory.singleFunctor A 0).obj M))
    (hN : P ((DerivedCategory.singleFunctor A 0).obj N))
    (hI : P ((DerivedCategory.singleFunctor A 0).obj (image f))) :
    P ((DerivedCategory.singleFunctor A 0).obj (kernel f)) ∧
      P ((DerivedCategory.singleFunctor A 0).obj (cokernel f)) := by
  let k := kernel.ι f
  let q := factorThruImage f
  have hkq : k ≫ q = 0 := by
    apply (cancel_mono (image.ι f)).mp
    simp only [k, q, Category.assoc, image.fac, kernel.condition, zero_comp]
  have hS : (ShortComplex.mk k q hkq).ShortExact := by
    let φ : ShortComplex.mk k q hkq ⟶
        ShortComplex.mk (kernel.ι f) f (kernel.condition f) :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := image.ι f
        comm₂₃ := by simp only [q, Category.id_comp, image.fac] }
    exact { exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (ShortComplex.exact_kernel f) }
  have hiz : image.ι f ≫ cokernel.π f = 0 := by
    apply (cancel_epi (factorThruImage f)).mp
    simp only [← Category.assoc, image.fac, cokernel.condition, comp_zero]
  have hT : (ShortComplex.mk (image.ι f) (cokernel.π f) hiz).ShortExact := by
    let φ : ShortComplex.mk f (cokernel.π f) (cokernel.condition f) ⟶
        ShortComplex.mk (image.ι f) (cokernel.π f) hiz :=
      { τ₁ := factorThruImage f
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    exact { exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (ShortComplex.exact_cokernel f) }
  exact ⟨P.ext_of_isTriangulatedClosed₁ _ hS.singleTriangle_distinguished hM hI,
    P.ext_of_isTriangulatedClosed₃ _ hT.singleTriangle_distinguished hI hN⟩

private theorem three_term_heart_generation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsSupportedImageGenerationClass Λ X P)
    (himage : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (f : M ⟶ N),
      IsConstantModelConstructible Λ X M → IsConstantModelConstructible Λ X N →
        P ((DerivedCategory.singleFunctor _ 0).obj (image f)))
    (K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (hK : ∀ n : ℤ, IsConstantModelConstructible Λ X (K.X n)) :
    P ((DerivedCategory.singleFunctor _ 0).obj (K.homology 0)) := by
  have : P.IsTriangulated := hP.1
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  let F := DerivedCategory.singleFunctor
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) 0
  have hZ : P (F.obj (K.cycles 0)) := by
    have hk := (single_relations_of_image P (K.d 0 1)
      (constructible_generation Λ X _ (hK 0) P hP)
      (constructible_generation Λ X _ (hK 1) P hP)
      (himage _ _ _ (hK 0) (hK 1))).1
    exact P.prop_of_iso (F.mapIso ((K.cyclesIsKernel (i := 0) (j := 1)
      (by simp)).conePointUniqueUpToIso (kernelIsKernel (K.d 0 1)))).symm hk
  let t := K.toCycles (-1) 0
  have ht : P (F.obj (image t)) := by
    have e : image (K.d (-1) 0) ≅ image t :=
      (image.isoStrongEpiMono (f := K.d (-1) 0) (factorThruImage t)
        (image.ι t ≫ K.iCycles 0)
        (by simp only [← Category.assoc, image.fac]; exact K.toCycles_i (-1) 0)).symm
    exact P.prop_of_iso (F.mapIso e) (himage _ _ _ (hK (-1)) (hK 0))
  have hw : image.ι t ≫ K.homologyπ 0 = 0 := by
    apply (cancel_epi (factorThruImage t)).mp
    simp [t, HomologicalComplex.toCycles_comp_homologyπ]
  have hs : (ShortComplex.mk (image.ι t) (K.homologyπ 0) hw).ShortExact := by
    let S := ShortComplex.mk t (K.homologyπ 0) (K.toCycles_comp_homologyπ (-1) 0)
    let T := ShortComplex.mk (image.ι t) (K.homologyπ 0) hw
    let φ : S ⟶ T :=
      { τ₁ := factorThruImage t
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    refine { exact := ?_ }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
      (S.exact_of_g_is_cokernel (K.homologyIsCokernel (i := -1) (j := 0) (by simp)))
  exact P.ext_of_isTriangulatedClosed₃ _ hs.singleTriangle_distinguished ht hZ

private theorem ind_finite_heart_generation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : indFiniteConstructibleComplexHearts Λ X M)
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsSupportedImageGenerationClass Λ X P)
    (himage : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (f : M ⟶ N),
      IsConstantModelConstructible Λ X M → IsConstantModelConstructible Λ X N →
        P ((DerivedCategory.singleFunctor _ 0).obj (image f))) :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨I, hI, hf, pres, hpres⟩ := hM
  let := hI
  let := hf
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  have := single_inverse_filtered Λ X P hP I
  apply (P.inverseImage (DerivedCategory.singleFunctor _ 0)).prop_of_isColimit
    pres.isColimit
  intro i
  obtain ⟨K, hK, ⟨e⟩⟩ := hpres i
  exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e).symm
    (three_term_heart_generation Λ X P hP himage K hK.2)

/-- The degree-zero supported hull contains the constructible generators and is closed
under extensions, filtered colimits, and small coproducts.

Source: the finite-tree and colimit parts of the proof of
`lem-sfb-weak-serre-supported-derived-generation`.
(blueprint: lem-sfb-supported-generation-heart-colimits).

Proof: reconstruct a constructible module by the localization short exact sequences
of a finite factoring open-closed tree. A short exact sequence gives a distinguished
triangle of degree-zero complexes. The degree-zero complex functor preserves
filtered colimits, with termwise lower bound zero. Finally a coproduct is the
filtered colimit of its finite partial sums, and extensions give the finite sums.
Intersect these assertions over all admissible derived classes. No coefficient or
Noetherian hypothesis is needed. This does not assert kernel or cokernel closure. -/
theorem supportedGeneration_heart_colimits
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    let H := (supportedImageGenerationHull Λ X).inverseImage
      (DerivedCategory.singleFunctor _ 0)
    IsConstantModelConstructible Λ X ≤ H ∧
      H.IsClosedUnderExtensions ∧
      (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
        H.IsClosedUnderColimitsOfShape I) ∧
      ∀ I : Type (u + 1), H.IsClosedUnderColimitsOfShape (Discrete I) := by
  let H := (supportedImageGenerationHull Λ X).inverseImage
    (DerivedCategory.singleFunctor _ 0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M hM P hP
    exact constructible_generation Λ X M hM P hP
  · constructor
    intro S hS h₁ h₃ P hP
    have := single_inverse_extensions Λ X P hP
    exact (P.inverseImage (DerivedCategory.singleFunctor _ 0)).prop_X₂_of_shortExact hS
      (h₁ P hP) (h₃ P hP)
  · intro I _ _
    constructor
    rintro M ⟨pres⟩ P hP
    have := single_inverse_filtered Λ X P hP I
    exact (P.inverseImage (DerivedCategory.singleFunctor _ 0)).prop_of_isColimit
      pres.isColimit (fun i ↦ pres.prop_diag_obj i P hP)
  · intro I
    constructor
    rintro M ⟨pres⟩ P hP
    have := single_inverse_coproducts Λ X P hP I
    exact (P.inverseImage (DerivedCategory.singleFunctor _ 0)).prop_of_isColimit
      pres.isColimit (fun i ↦ pres.prop_diag_obj i P hP)

/-- Filtered colimits of constructible modules belong to the supported derived hull.

Source: finite open-closed refinement and the strict filtered-colimit clause of
`lem-sfb-weak-serre-supported-derived-generation`.
(blueprint: lem-sfb-ind-constructible-supported-generation).

Proof: refine the finite stratification of each constructible stage by a finite
qcqs open-closed tree. Exact open extension and closed direct image, together with
the localization short exact sequence, reconstruct that stage from the supported
finite scalar leaf models. Apply the common-bound filtered-colimit clause to the
complexes concentrated in degree zero, using lower bound zero. This works for
arbitrary condensed commutative rings, including zero, without Noetherianity. -/
theorem indConstructible_mem_supported_derived_generation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) M)
    : supportedImageGenerationHull Λ X
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  intro P hP
  obtain ⟨I, hI, hf, pres, hpres⟩ := hM
  let := hI
  let := hf
  have := single_inverse_filtered Λ X P hP I
  exact (P.inverseImage (DerivedCategory.singleFunctor _ 0)).prop_of_isColimit
    pres.isColimit (fun i ↦ constructible_generation Λ X _ (hpres i) P hP)

/-- Filtered colimits of finite constructible complex hearts lie in the supported hull.

Source: the finite-model relation step of
`lem-sfb-weak-serre-supported-derived-generation`, blueprint latest,
`det-sf-comp-coherence-refinement.proof.md`, (2), first paragraph.
(blueprint: lem-sfb-ind-finite-heart-supported-generation).

Proof: refine two constructible stratifications simultaneously by a finite qcqs
open-closed tree. Exact pullback identifies each restriction of an image with the
image of the restricted map. At every leaf apply the supported finite-model image
theorem. The localization short exact sequences reconstruct the global image.
For a complex K use the two sequences from K^0 to its image and from its cycles
to H^0(K). Its boundaries are isomorphic to the image of d^-1. Distinguished
triangles therefore put H^0(K)[0] in every admissible class. Apply the strict
filtered-colimit clause to the degree-zero complexes of the given presentation,
all with termwise lower bound zero. No closure assertion about this heart class
under arbitrary kernels is made. -/
theorem indFiniteHeart_mem_supported_derived_generation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : indFiniteConstructibleComplexHearts Λ X M) :
    supportedImageGenerationHull Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  intro P hP
  apply ind_finite_heart_generation Λ X M hM P hP
  intro N L f hN hL
  apply constructible_image_generation Λ X P hP ?_ N L f hN hL
  intro tree S p N L f hN hL
  exact supported_image_mem_bounded_derived_generation Λ ℓ
    hΛ tree p N L hN hL f P hP

/-- The finite discrete coefficient branch holds over every qcqs scheme.

Source: Stacks Tags 03SA(3), 099Y, finite discrete comparison, and the
finite-complex-heart step of the supported-generation node.
(blueprint: lem-sfb-finite-coefficient-supported-generation).

Proof: finite discrete comparison supplies a filtered presentation by constructible
modules, each regarded as the heart of its degree-zero complex. Apply the proved
ind-finite-heart supported-generation theorem with this presentation and the given
finite coefficient ring isomorphism. No Noetherianity is required. The finite ring
may be zero and the affine or qcqs base may be empty. -/
theorem finiteCoefficient_weakSerre_mem_supported_derived_generation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A]
    (htors : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M) :
    supportedImageGenerationHull Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  exact indFiniteHeart_mem_supported_derived_generation Λ ℓ
    (Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, htors, ⟨e⟩⟩) X M
    (finiteCoefficient_serre_is_indFiniteHeart A Λ e X M hM)

/-- The Noetherian specialization retains all five coefficient families.

Source: Hemo--Richarz--Scholbach, Theorem 6.2(3), Lemmas 5.3 and 8.6,
and the Noetherian finite-complex-heart closure node.
(blueprint: lem-sfb-noetherian-supported-generation).

Proof: the Noetherian finite-complex-heart closure theorem gives a replete class
containing the constructible generators and closed under kernels, cokernels,
extensions and all small coproducts. Minimality of the weak Serre coproduct closure
therefore puts M in this class. Apply ind-finite-heart supported generation.
No Noetherianity is inferred from the qcqs assumptions of the unrestricted theorem. -/
theorem noetherian_weakSerre_mem_supported_derived_generation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M) :
    supportedImageGenerationHull Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let H : ObjectProperty _ := indFiniteConstructibleComplexHearts Λ X
  obtain ⟨_, hgen, hk, hc, he, hcop⟩ :=
    noetherian_finite_complex_heart_filtered_closure ℓ Λ
      hΛ X
  have : H.IsClosedUnderIsomorphisms :=
    inferInstanceAs (ObjectProperty.ind _).IsClosedUnderIsomorphisms
  exact indFiniteHeart_mem_supported_derived_generation Λ ℓ hΛ X M
    (hM H hgen inferInstance hk hc he hcop)

/-- Membership in the tree-path hull descends from weakly contractible affine charts.

Source: support-chain descent step of the supported-generation plan.
(blueprint: lem-sfb-supported-image-hull-proetale-descent).

Proof: compare the tree-path hull with the chain hull on X and on every affine
cover member. Each affine chart is qcqs. The existing supported-model-hull descent
theorem then applies to the actual upperStar restriction of M. Convert its conclusion
back using the proved hull comparison. This uses the declared descent obligation;
it does not infer hull membership from conservativity alone. -/
theorem supportedImageHull_proetale_descent
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (I : Type (u + 1)) (U : I → X.ProEt)
    (hcover : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      Scheme.proetalePrecoverage.coverings X)
    (haffine : ∀ i : I, IsAffine (U i).left)
    (hcontract : ∀ i : I,
      (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} (U i))
    (hlocal : ∀ i : I, supportedImageGenerationHull Λ (U i).left
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ (U i).hom).obj M))) :
    supportedImageGenerationHull Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  apply (supportedModelHull_iff Λ X _).mp
  apply supportedModelHull_proetale_descent ℓ Λ hΛ X M I U hcover haffine hcontract
  intro i
  have := haffine i
  exact (supportedModelHull_iff Λ (U i).left _).mpr (hlocal i)

/-- The constructibly generated weak Serre coproduct heart embeds, in degree zero,
into the supported derived model hull. This is a structural obligation: it mentions
neither a closed immersion nor its torsion cohomology or restriction transformation.

Source: the coefficient-generation step of the agent-formulated obligation below
blueprint latest, `det-sf-comp-coherence-refinement.proof.md`, (2), first paragraph.
An exact reference at this generality is WANTED.
(blueprint: lem-sfb-weak-serre-supported-derived-generation).

Proof status: the finite discrete branch, the Noetherian specialization, and
membership for the ind-finite-complex-heart class are proved above. The
unrestricted topological-coefficient relation-resolution step remains open.
The theorem below retains its original statement and single named hole.

Proof plan:

1. Fix an admissible derived class H in the intersection defining the supported hull.
Use finite constructible open-closed refinement on the stratification of a generator.
At each leaf its restriction is a finite scalar local model. Exact extension along
the path and the open-closed localization sequence reconstruct the generator by
finitely many distinguished triangles. Thus its degree-zero object is in H.

2. Establish the relation-resolution assertion needed for kernels and cokernels in
the heart generated by these supported models. This must cover arbitrary actual
module maps, including continuous matrices on profinite component spaces. Finite
model images are already covered by supported_image_mem_bounded_derived_generation;
iteration through kernels of maps between previously constructed heart objects is
an additional obligation. Use strict relation resolutions on affine weakly
contractible pro-etale charts, products of the finite truncations, and their
common-bound filtered colimits. The resulting objects must be the actual abelian
kernels and cokernels in degree zero. Triangle closure alone does not prove this
assertion; neither does the theorem about images between two finite local models.

3. Translate paths to finite support chains and complete chains by complementary
sibling leaves to compare the two existing hull definitions. Their filtered clauses
agree since IsStrictlyGE means terms below the bound vanish. Descend those local
relation resolutions using supported-hull pro-etale descent, retaining the actual
support functors. Short exact sequences give triangle closure
for extensions. A coproduct is the filtered colimit of its finite partial sums,
placed in degree zero, so the specified strict filtered-colimit closure handles it.
These constructions show that the degree-zero inverse image of the supported hull
has all four weak Serre coproduct closure properties and contains every generator.
Minimality of weakSerreCoproductClosure gives the assertion.

The relation-resolution assertion in step 2 is not supplied by the invalid arbitrary-
qcqs finite-complex-heart approximation: its repaired version requires Noetherianity.
In particular this statement does not claim that the module is a filtered colimit
of hearts of finite constructible complexes. Empty schemes, zero modules, and zero
rings use the zero object; the identity support path is allowed. -/
theorem weakSerre_mem_supported_derived_generation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M) :
    supportedImageGenerationHull Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
