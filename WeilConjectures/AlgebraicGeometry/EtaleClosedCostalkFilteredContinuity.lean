/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.RightDerivedUniformFilteredContinuity
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.EtaleClosedSupportTriangle
import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeColimit
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit

/-! # Uniformly bounded-below continuity of ordinary étale closed costalks

Source: Stacks Project, Tag 09XQ and the subsequent derived support triangle;
Bhatt–Scholze, Lemma 6.3.14, closed-factor argument
(blueprint: lem-per-etale-closed-costalk-filtered-continuity).

Filtered colimits here are exact termwise colimits of compatible complex models.
A model includes its natural identification with the recorded ambient right adjoint.
The comparison is the localized chain-level cocone map followed by that identification.

## Main definitions

* `AlgebraicGeometry.Etale.closedCostalkFilteredComparison`

## Main statements

* `AlgebraicGeometry.Etale.closedLowerStar_filtered_exact`
* `AlgebraicGeometry.Etale.closedCostalk_isGE`
* `AlgebraicGeometry.Etale.exists_closedCostalk_complexModel`
* `AlgebraicGeometry.Etale.closedCostalkFilteredComparison_isIso`
* `AlgebraicGeometry.Etale.closedCostalkFilteredComparison_naturality`
* `AlgebraicGeometry.Etale.closedCostalkFilteredComparison_representative_independence`
-/

set_option autoImplicit false

@[expose] public section

universe u v w

open CategoryTheory Limits Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Exactness and filtered-colimit preservation of closed direct image, together with
its identification with the termwise derived functor.
Source: Stacks Project, Tag 09XQ and its derived support triangle;
Bhatt–Scholze, Lemma 6.3.14 (closed factor)
(blueprint: lem-per-etale-closed-costalk-filtered-continuity).

Proof: For the canonical open complement, the ModuleCat-valued supported-kernel
adjunction (lem-pur-etale-supported-kernel-adjunction) makes closed direct image a left
adjoint, so it preserves all colimits, in particular finite and filtered ones
(lem-weil-pbc-left-adjoint-preserves-colimits). The same adjunction applied degreewise
makes the termwise functor on cochain complexes a left adjoint, giving the filtered-colimit
assertion on complexes. A closed immersion is finite, and finite direct image is exact
(lemma-weil-pbc-finite-direct-image-exact); hence its total right-derived unit is an
isomorphism. -/
theorem closedLowerStar_filtered_exact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i) ∧
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (lowerStar (ModuleCat.{u + 1} A) i) ∧
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      ((lowerStar (ModuleCat.{u + 1} A) i).mapHomologicalComplex (ComplexShape.up ℤ)) ∧
    IsIso (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorUnit := by
  let C := ModuleCat.{u + 1} A
  let W : X.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  let adj := lowerStarClosedUpperShriekAdjunction C i W.ι hij
  have : (lowerStar C i).IsLeftAdjoint := adj.isLeftAdjoint
  have : ((lowerStar C i).mapHomologicalComplex (.up ℤ)).IsLeftAdjoint :=
    (adj.mapHomologicalComplex (.up ℤ)).isLeftAdjoint
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The ambient closed costalk preserves every lower cohomological bound.
Source: Stacks Project, Tag 09XQ and its derived support triangle;
Bhatt–Scholze, Lemma 6.3.14 (closed factor)
(blueprint: lem-per-etale-closed-costalk-filtered-continuity).

Proof: Uniqueness of right adjoints identifies the ambient costalk with the right
derived supported-kernel functor. Regard K as a bounded-below object and use compatibility
of the bounded-below and unbounded right derived functors. The standard lower-bound
vanishing theorem then gives the required vanishing in every degree below r. -/
theorem closedCostalk_isGE
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (r : ℤ) (K : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) (hK : K.IsGE r) :
    ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K).IsGE r := by
  let C := ModuleCat.{u + 1} A
  let W : X.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  let F := closedUpperShriek C i W.ι
  let e := (derivedLowerStarClosedUpperShriekAdjunction (R := A) i W.ι hij).rightAdjointUniq
    (Adjunction.ofIsLeftAdjoint (R(lowerStar C i)))
  have : K.IsGE r := hK
  let Kp : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology C) :=
    ⟨K, ⟨r, inferInstance⟩⟩
  have : Kp.IsGE r := (Kp.isGE_ι_obj_iff r).1 hK
  have hF : (F.rightDerivedFunctor.obj K).IsGE r := by
    apply (_root_.DerivedCategory.isGE_iff _ r).2
    intro q hq
    exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE Kp r hq).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        (F.rightDerivedFunctorPlusCompatibility.app Kp)).symm
  have : _root_.DerivedCategory.TStructure.t.IsGE (F.rightDerivedFunctor.obj K) r := hF
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso (e.app K) r

/-- Compatible functorial complex representatives for the ambient closed costalk exist.
Source: Stacks Project, Tag 09XQ and its derived support triangle;
Bhatt–Scholze, Lemma 6.3.14 (closed factor)
(blueprint: lem-per-etale-closed-costalk-filtered-continuity).

Proof: Choose functorial K-injective resolutions with injective terms and apply the
abelian supported-kernel right adjoint termwise. Exactness of closed pushforward makes
this the derived right adjoint. Uniqueness of right adjoints identifies it naturally with
the ambient right adjoint recorded by lem-exc-closed-ambient. -/
theorem exists_closedCostalk_complexModel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ T : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
        CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      Nonempty (T ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
        (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint) := by
  let C := ModuleCat.{u + 1} A
  let B := Sheaf X.smallEtaleTopology C
  let W : X.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  let F := closedUpperShriek C i W.ι
  let I := CochainComplex.kInjectiveResolutionFunctor.{u + 1} B
  let η := CochainComplex.toKInjectiveResolution.{u + 1} B
  let e := (derivedLowerStarClosedUpperShriekAdjunction (R := A) i W.ι hij).rightAdjointUniq
    (Adjunction.ofIsLeftAdjoint (R(lowerStar C i)))
  have hη : IsIso (Functor.whiskerRight η _root_.DerivedCategory.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} B M).2
  have hF : IsIso (Functor.whiskerLeft (I ⋙ HomotopyCategory.quotient _ _)
      F.rightDerivedFunctorUnit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    dsimp only [Functor.whiskerLeft_app, Functor.comp_obj]
    infer_instance
  refine ⟨I ⋙ F.mapHomologicalComplex (.up ℤ), ⟨?_⟩⟩
  exact (Functor.isoWhiskerLeft I
      ((Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
          _root_.DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
          (_root_.DerivedCategory.quotientCompQhIso _)).symm) ≪≫
    asIso (Functor.whiskerLeft (I ⋙ HomotopyCategory.quotient _ _)
      F.rightDerivedFunctorUnit) ≪≫
    Functor.isoWhiskerLeft I
      (Functor.isoWhiskerRight (_root_.DerivedCategory.quotientCompQhIso B)
        F.rightDerivedFunctor) ≪≫
    Functor.isoWhiskerRight (asIso (Functor.whiskerRight η _root_.DerivedCategory.Q)).symm
      F.rightDerivedFunctor ≪≫
    Functor.isoWhiskerLeft _root_.DerivedCategory.Q e)

/-- The canonical closed-costalk comparison from a termwise colimit of compatible
functorial representatives. `e` is the natural derived identification of the model `T`.
No map is chosen: the original cocone is mapped by `T`, its universal map is localized,
and `e` identifies its target with the ambient closed costalk.
Source: Stacks Project, Tag 09XQ, derived support functor and cocone construction
(blueprint: lem-per-etale-closed-costalk-filtered-continuity). -/
noncomputable def closedCostalkFilteredComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (e : T ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (c : Cocone N) :
    _root_.DerivedCategory.Q.obj (colimit (N ⋙ T)) ⟶
      (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj (_root_.DerivedCategory.Q.obj c.pt) :=
  _root_.DerivedCategory.Q.map (colimit.desc (N ⋙ T) (T.mapCocone c)) ≫ e.hom.app c.pt

-- The following private colimit and five-lemma calculations are the generic part of
-- CondensedClosedCostalkDerivedContinuity, specialized below to ordinary etale sheaves.
private noncomputable def triangleComparison
    {C A I : Type*} [Category* C] [Category* A] [Category I]
    [HasShift C ℤ] [Abelian A] [HasColimitsOfShape I A]
    (T : I ⥤ Triangle C) (c : Cocone T) (F : C ⥤ A) [F.ShiftSequence ℤ] (n : ℤ)
    (π : Triangle C ⥤ C) :
    colimit (T ⋙ π ⋙ F.shift n) ⟶ (F.shift n).obj (π.obj c.pt) :=
  colimit.desc _ ((π ⋙ F.shift n).mapCocone c)

private theorem triangleComparison_isIso
    {C A I : Type*} [Category* C] [Category* A] [Category I]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Abelian A] [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (T : I ⥤ Triangle C) (c : Cocone T)
    (hT : ∀ s, T.obj s ∈ distTriang C) (hc : c.pt ∈ distTriang C)
    (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]
    (m n : ℤ) (h : m + 1 = n)
    [IsIso (triangleComparison T c F m Triangle.π₂)]
    [IsIso (triangleComparison T c F m Triangle.π₃)]
    [IsIso (triangleComparison T c F n Triangle.π₂)]
    [IsIso (triangleComparison T c F n Triangle.π₃)] :
    IsIso (triangleComparison T c F n Triangle.π₁) := by
  let A₀ := T ⋙ Triangle.π₂ ⋙ F.shift m
  let A₁ := T ⋙ Triangle.π₃ ⋙ F.shift m
  let A₂ := T ⋙ Triangle.π₁ ⋙ F.shift n
  let A₃ := T ⋙ Triangle.π₂ ⋙ F.shift n
  let A₄ := T ⋙ Triangle.π₃ ⋙ F.shift n
  let d₀ : A₀ ⟶ A₁ :=
    Functor.whiskerRight (Functor.whiskerLeft T Triangle.π₂Toπ₃) (F.shift m)
  let d₁ : A₁ ⟶ A₂ :=
    { app s := F.homologySequenceδ (T.obj s) m n h
      naturality _ _ f := F.homologySequenceδ_naturality _ _ (T.map f) m n h }
  let d₂ : A₂ ⟶ A₃ :=
    Functor.whiskerRight (Functor.whiskerLeft T Triangle.π₁Toπ₂) (F.shift n)
  let d₃ : A₃ ⟶ A₄ :=
    Functor.whiskerRight (Functor.whiskerLeft T Triangle.π₂Toπ₃) (F.shift n)
  have z₀ : d₀ ≫ d₁ = 0 := by
    ext s
    exact F.comp_homologySequenceδ (T.obj s) (hT s) m n h
  have z₁ : d₁ ≫ d₂ = 0 := by
    ext s
    exact F.homologySequenceδ_comp (T.obj s) (hT s) m n h
  have z₂ : d₂ ≫ d₃ = 0 := by
    ext s
    exact F.homologySequence_comp (T.obj s) (hT s) n
  have e₀ : (ShortComplex.mk d₀ d₁ z₀).Exact :=
    (ShortComplex.exact_iff_evaluation _).2
      (fun s ↦ F.homologySequence_exact₃ (T.obj s) (hT s) m n h)
  have e₁ : (ShortComplex.mk d₁ d₂ z₁).Exact :=
    (ShortComplex.exact_iff_evaluation _).2
      (fun s ↦ F.homologySequence_exact₁ (T.obj s) (hT s) m n h)
  have e₂ : (ShortComplex.mk d₂ d₃ z₂).Exact :=
    (ShortComplex.exact_iff_evaluation _).2
      (fun s ↦ F.homologySequence_exact₂ (T.obj s) (hT s) n)
  let R := ComposableArrows.mk₄ (colim.map d₀) (colim.map d₁)
    (colim.map d₂) (colim.map d₃)
  have hR : R.Exact :=
    ComposableArrows.exact_of_δ₀ (e₀.map colim).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀ (e₁.map colim).exact_toComposableArrows
        (e₂.map colim).exact_toComposableArrows)
  let R' := ComposableArrows.mk₄ ((F.shift m).map c.pt.mor₂)
    (F.homologySequenceδ c.pt m n h) ((F.shift n).map c.pt.mor₁)
    ((F.shift n).map c.pt.mor₂)
  have hR' : R'.Exact :=
    ComposableArrows.exact_of_δ₀
      (F.homologySequence_exact₃ c.pt hc m n h).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (F.homologySequence_exact₁ c.pt hc m n h).exact_toComposableArrows
        (F.homologySequence_exact₂ c.pt hc n).exact_toComposableArrows)
  let φ : R ⟶ R' := ComposableArrows.homMk₄
    (triangleComparison T c F m Triangle.π₂)
    (triangleComparison T c F m Triangle.π₃)
    (triangleComparison T c F n Triangle.π₁)
    (triangleComparison T c F n Triangle.π₂)
    (triangleComparison T c F n Triangle.π₃)
    (by
      change colimMap d₀ ≫ triangleComparison T c F m Triangle.π₃ =
        triangleComparison T c F m Triangle.π₂ ≫ (F.shift m).map c.pt.mor₂
      apply colimit.hom_ext
      intro s
      dsimp only [A₀, A₁, A₂, A₃, A₄]
      simp only [triangleComparison, ι_colimMap_assoc, colimit.ι_desc,
        colimit.ι_desc_assoc]
      change (F.shift m).map (T.obj s).mor₂ ≫
          (F.shift m).map (c.ι.app s).hom₃ =
        (F.shift m).map (c.ι.app s).hom₂ ≫ (F.shift m).map c.pt.mor₂
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (F.shift m).map (c.ι.app s).comm₂)
    (by
      change colimMap d₁ ≫ triangleComparison T c F n Triangle.π₁ =
        triangleComparison T c F m Triangle.π₃ ≫ F.homologySequenceδ c.pt m n h
      apply colimit.hom_ext
      intro s
      dsimp only [A₀, A₁, A₂, A₃, A₄]
      simp only [triangleComparison, ι_colimMap_assoc, colimit.ι_desc,
        colimit.ι_desc_assoc]
      exact (F.homologySequenceδ_naturality _ _ (c.ι.app s) m n h).symm)
    (by
      change colimMap d₂ ≫ triangleComparison T c F n Triangle.π₂ =
        triangleComparison T c F n Triangle.π₁ ≫ (F.shift n).map c.pt.mor₁
      apply colimit.hom_ext
      intro s
      dsimp only [A₀, A₁, A₂, A₃, A₄]
      simp only [triangleComparison, ι_colimMap_assoc, colimit.ι_desc,
        colimit.ι_desc_assoc]
      change (F.shift n).map (T.obj s).mor₁ ≫
          (F.shift n).map (c.ι.app s).hom₂ =
        (F.shift n).map (c.ι.app s).hom₁ ≫ (F.shift n).map c.pt.mor₁
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (F.shift n).map (c.ι.app s).comm₁)
    (by
      change colimMap d₃ ≫ triangleComparison T c F n Triangle.π₃ =
        triangleComparison T c F n Triangle.π₂ ≫ (F.shift n).map c.pt.mor₂
      apply colimit.hom_ext
      intro s
      dsimp only [A₀, A₁, A₂, A₃, A₄]
      simp only [triangleComparison, ι_colimMap_assoc, colimit.ι_desc,
        colimit.ι_desc_assoc]
      change (F.shift n).map (T.obj s).mor₂ ≫
          (F.shift n).map (c.ι.app s).hom₃ =
        (F.shift n).map (c.ι.app s).hom₂ ≫ (F.shift n).map c.pt.mor₂
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (F.shift n).map (c.ι.app s).comm₂)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR hR' φ
    (by change Epi (triangleComparison T c F m Triangle.π₂); infer_instance)
    (by change IsIso (triangleComparison T c F m Triangle.π₃); infer_instance)
    (by change IsIso (triangleComparison T c F n Triangle.π₂); infer_instance)
    (by change Mono (triangleComparison T c F n Triangle.π₃); infer_instance)

private theorem comparison_ofNatIso
    {C A I : Type*} [Category* C] [Category* A] [Category I]
    [HasColimitsOfShape I A] (D : I ⥤ C) (c : Cocone D)
    {F G : C ⥤ A} (e : F ≅ G)
    [IsIso (colimit.desc (D ⋙ F) (F.mapCocone c))] :
    IsIso (colimit.desc (D ⋙ G) (G.mapCocone c)) := by
  have heq : colimMap (Functor.whiskerLeft D e.hom) ≫
      colimit.desc (D ⋙ G) (G.mapCocone c) =
    colimit.desc (D ⋙ F) (F.mapCocone c) ≫ e.hom.app c.pt := by
    apply colimit.hom_ext
    intro s
    simp only [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
    exact (e.hom.naturality (c.ι.app s)).symm
  have hi : IsIso (colimMap (Functor.whiskerLeft D e.hom)) :=
    inferInstanceAs (IsIso (colim.map (Functor.whiskerLeft D e.hom)))
  have : IsIso (colimMap (Functor.whiskerLeft D e.hom) ≫
      colimit.desc (D ⋙ G) (G.mapCocone c)) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (colimMap (Functor.whiskerLeft D e.hom))
    (colimit.desc (D ⋙ G) (G.mapCocone c))

private noncomputable def localizationTriangleFunctor
    {C : Type*} [Category* C] [HasShift C ℤ]
    (F G : C ⥤ C) (f : F ⟶ 𝟭 C) (g : 𝟭 C ⟶ G)
    (δ : G ⟶ F ⋙ shiftFunctor C (1 : ℤ)) : C ⥤ Triangle C where
  obj K := Triangle.mk (f.app K) (g.app K) (δ.app K)
  map k :=
    { hom₁ := F.map k
      hom₂ := k
      hom₃ := G.map k
      comm₁ := (f.naturality k).symm
      comm₂ := (g.naturality k).symm
      comm₃ := (δ.naturality k).symm }
  map_id K := by ext <;> simp [Triangle.mk]
  map_comp k l := by ext <;> simp


-- The resolution-unit comparison is the generic construction in
-- ClosedSupportBoundedContinuity; its two factors are canonical natural isomorphisms.
private noncomputable def resolutionDerivedIso
    {A : Type v} [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    [HasDerivedCategory.{w} A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] :
    DerivedCategory.Q ⋙ F.rightDerivedFunctor ≅
      CochainComplex.kInjectiveResolutionFunctor.{u} A ⋙
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let R := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let α : R ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      R ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    Functor.whiskerLeft R
      (Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
          (DerivedCategory.quotientCompQhIso B).inv ≫
        Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv
          DerivedCategory.Qh ≫
        Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
          F.rightDerivedFunctorUnit ≫
        Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom F.rightDerivedFunctor)
  have : IsIso α := by
    have (K : CochainComplex A ℤ) : IsIso (α.app K) := by
      dsimp [α]
      infer_instance
    exact NatIso.isIso_of_isIso_app α
  let γ : DerivedCategory.Q (C := A) ⟶ R ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (CochainComplex.toKInjectiveResolution.{u} A) DerivedCategory.Q
  have : IsIso γ := by
    have (K : CochainComplex A ℤ) : IsIso (γ.app K) := by
      have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} A).app K) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A K).2
      change IsIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{u} A).app K))
      infer_instance
    exact NatIso.isIso_of_isIso_app γ
  exact Functor.isoWhiskerRight (asIso γ) F.rightDerivedFunctor ≪≫ (asIso α).symm


private theorem comparison_of_colimitCocone
    {C B I : Type*} [Category* C] [Category* B] [Category I]
    [HasColimitsOfShape I B] (N : I ⥤ C) (c c' : Cocone N)
    (hc : IsColimit c) (hc' : IsColimit c') (F : C ⥤ B)
    [IsIso (colimit.desc (N ⋙ F) (F.mapCocone c))] :
    IsIso (colimit.desc (N ⋙ F) (F.mapCocone c')) := by
  let e := hc.coconePointUniqueUpToIso hc'
  have h : colimit.desc (N ⋙ F) (F.mapCocone c') =
      colimit.desc (N ⋙ F) (F.mapCocone c) ≫ F.map e.hom := by
    apply colimit.hom_ext
    intro j
    simp only [colimit.ι_desc, colimit.ι_desc_assoc, Functor.mapCocone_ι_app,
      ← F.map_comp]
    exact congrArg F.map (hc.comp_coconePointUniqueUpToIso_hom hc' j).symm
  rw [h]
  infer_instance

private theorem rightDerivedComparison_homology
    {B : Type*} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{v} B]
    {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [HasDerivedCategory.{v} C]
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F]
    (hF : ∀ p : ℕ, PreservesFilteredColimitsOfSize.{v, v} (F.rightDerived p))
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (N : J ⥤ CochainComplex B ℤ) (c : Cocone N) (hc : IsColimit c)
    (r : ℤ) (hN : ∀ j, (_root_.DerivedCategory.Q.obj (N.obj j)).IsGE r) (q : ℤ) :
    IsIso (colimit.desc (N ⋙ _root_.DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙
      _root_.DerivedCategory.homologyFunctor C q)
      ((_root_.DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙
        _root_.DerivedCategory.homologyFunctor C q).mapCocone c)) := by
  let L := F.kInjectiveFilteredFunctor
  have hL : IsIso (_root_.DerivedCategory.Q.map (colimit.post N L)) :=
    (F.rightDerived_uniform_filtered_continuity hF J N r hN).1
  have hq : QuasiIso (colimit.post N L) :=
    (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hL
  let H := HomologicalComplex.homologyFunctor C (.up ℤ) q
  have : IsIso (H.map (colimit.post N L)) := by
    exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap (colimit.post N L) q))
  have h : IsIso (colimit.post N (L ⋙ H)) := by
    rw [← colimit.post_post]
    infer_instance
  change IsIso (colimit.desc (N ⋙ (L ⋙ H))
    ((L ⋙ H).mapCocone (colimit.cocone N))) at h
  let e : _root_.DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙
      _root_.DerivedCategory.homologyFunctor C q ≅ L ⋙ H :=
    Functor.isoWhiskerRight (resolutionDerivedIso F)
      (_root_.DerivedCategory.homologyFunctor C q) ≪≫
    Functor.isoWhiskerLeft L (_root_.DerivedCategory.homologyFunctorFactors C q)
  have hbase : IsIso (colimit.desc
      (N ⋙ _root_.DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙
        _root_.DerivedCategory.homologyFunctor C q)
      ((_root_.DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙
        _root_.DerivedCategory.homologyFunctor C q).mapCocone (colimit.cocone N))) :=
    comparison_ofNatIso N (colimit.cocone N) e.symm
  exact comparison_of_colimitCocone N (colimit.cocone N) c
    (colimit.isColimit N) hc _

set_option maxHeartbeats 800000 in
-- The five-lemma argument combines several derived-functor comparison isomorphisms.
/-- Uniformly bounded-below filtered continuity for any compatible functorial model
and any original termwise colimit cocone.
Source: Stacks Project, Tag 09XQ and its derived support triangle;
Bhatt–Scholze, Lemma 6.3.14 (closed factor)
(blueprint: lem-per-etale-closed-costalk-filtered-continuity).

Proof:
1. Module sheaves are Grothendieck abelian, so filtered colimits are exact and commute
with homology. They preserve compatible quasi-isomorphisms and the common lower bound.
2. The complementary open j is quasi-compact and quasi-separated since X is Noetherian.
Higher direct images R^p j_* preserve filtered colimits. The uniformly bounded-below
right-derived continuity theorem, applied to j_*, and exact colimit-preserving j^* give
continuity of Rj_*j^* without any common upper bound or cohomological-dimension bound.
3. Apply the natural support triangle to all original cocone legs. Take filtered colimits
of the long exact homology sequences. The middle and open comparisons are isomorphisms.
The five lemma in each degree makes the closed comparison a homology isomorphism.
4. Exact closed pushforward commutes with cohomology. As a fully faithful left adjoint it
preserves the filtered colimit and reflects isomorphisms, so the costalk cohomology
comparison is itself invertible. The support arrow is the adjunction counit, and its
naturality identifies all cocone legs.
5. Through e and the complex homology factorization, these cohomology comparisons are the
homology maps of colimit.desc (N ⋙ T) (T.mapCocone c). It is therefore a
quasi-isomorphism, Q inverts it, and composing with e gives the comparison defined here,
for every model (T, e). -/
theorem closedCostalkFilteredComparison_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (T : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (e : T ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (c : Cocone N)
    (hc : IsColimit c) (r : ℤ)
    (hN : ∀ (j : J) (q : ℤ), q < r → IsZero ((N.obj j).homology q)) :
    IsIso (closedCostalkFilteredComparison A i T e N c) := by
  classical
  let M := ModuleCat.{u + 1} A
  let B := Sheaf X.smallEtaleTopology M
  let C := Sheaf Z.smallEtaleTopology M
  let W : X.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  let j := W.ι
  let E := Sheaf W.toScheme.smallEtaleTopology M
  let ipush := lowerStar M i
  let jpush := lowerStar M j
  let jstar := upperStar M j
  let F := R(ipush)
  let G := D(jstar) ⋙ R(jpush)
  obtain ⟨δ, hδ⟩ := exists_etale_closedSupportTriangle A i j hij
  let loc := localizationTriangleFunctor (F.rightAdjoint ⋙ F) G
    (Adjunction.ofIsLeftAdjoint F).counit
    (mapDerivedUpperStarLowerStarAdjunction M j).unit δ
  let TT := N ⋙ _root_.DerivedCategory.Q ⋙ loc
  let tc := loc.mapCocone (_root_.DerivedCategory.Q.mapCocone c)
  have hTT (s : J) : TT.obj s ∈ distTriang (_root_.DerivedCategory B) := hδ _
  have htc : tc.pt ∈ distTriang (_root_.DerivedCategory B) := hδ _
  let H := _root_.DerivedCategory.homologyFunctor B 0
  have hid (q : ℤ) : IsIso (triangleComparison TT tc H q Triangle.π₂) := by
    let K := HomologicalComplex.homologyFunctor B (.up ℤ) q
    have : IsIso (colimit.desc (N ⋙ K) (K.mapCocone c)) :=
      (colimit.isColimit _).coconePointUniqueUpToIso (isColimitOfPreserves K hc)
        |>.isIso_hom
    exact comparison_ofNatIso N c (_root_.DerivedCategory.homologyFunctorFactors B q).symm
  have hopen (q : ℤ) : IsIso (triangleComparison TT tc H q Triangle.π₃) := by
    let K := jstar.mapHomologicalComplex (.up ℤ)
    let P := N ⋙ K
    let cp := K.mapCocone c
    have : K.IsLeftAdjoint :=
      ((upperStarLowerStarAdjunction M j).mapHomologicalComplex (.up ℤ)).isLeftAdjoint
    have hcp : IsColimit cp := isColimitOfPreserves K hc
    have hP (s : J) : (_root_.DerivedCategory.Q.obj (P.obj s)).IsGE r := by
      have hNs : (_root_.DerivedCategory.Q.obj (N.obj s)).IsGE r := by
        apply (_root_.DerivedCategory.isGE_iff _ r).2
        intro q hq
        exact (hN s q hq).of_iso
          ((_root_.DerivedCategory.homologyFunctorFactors B q).app (N.obj s))
      have := hNs
      have : _root_.DerivedCategory.TStructure.t.IsGE
          ((_root_.DerivedCategory.Q ⋙ D(jstar)).obj (N.obj s)) r :=
        jstar.isGE_mapDerivedCategory_obj (_root_.DerivedCategory.Q.obj (N.obj s)) r
      exact _root_.DerivedCategory.TStructure.t.isGE_of_iso
        (jstar.mapDerivedCategoryFactors.app (N.obj s)) r
    have hF (p : ℕ) :
        PreservesFilteredColimitsOfSize.{u + 1, u + 1} (jpush.rightDerived p) := by
      constructor
      intro I _ _
      have : PreservesColimitsOfShape I
          (_root_.DerivedCategory.Plus.singleFunctor E 0 ⋙ jpush.rightDerivedFunctorPlus ⋙
            _root_.DerivedCategory.Plus.homologyFunctor B (p : ℤ)) :=
        preservesColimitsOfShape_higherDirectImage_large A j p I
      exact preservesColimitsOfShape_of_natIso
        (jpush.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p)
    have : IsIso (colimit.desc
        (P ⋙ _root_.DerivedCategory.Q ⋙ R(jpush) ⋙
          _root_.DerivedCategory.homologyFunctor B q)
        ((_root_.DerivedCategory.Q ⋙ R(jpush) ⋙
          _root_.DerivedCategory.homologyFunctor B q).mapCocone cp)) :=
      rightDerivedComparison_homology jpush hF P cp hcp r hP q
    change IsIso (colimit.desc
      (N ⋙ (K ⋙ _root_.DerivedCategory.Q ⋙ R(jpush) ⋙
        _root_.DerivedCategory.homologyFunctor B q))
      ((K ⋙ _root_.DerivedCategory.Q ⋙ R(jpush) ⋙
        _root_.DerivedCategory.homologyFunctor B q).mapCocone c)) at this
    let eopen : K ⋙ _root_.DerivedCategory.Q ⋙ R(jpush) ⋙
        _root_.DerivedCategory.homologyFunctor B q ≅
      _root_.DerivedCategory.Q ⋙ G ⋙ _root_.DerivedCategory.homologyFunctor B q :=
      Functor.isoWhiskerRight jstar.mapDerivedCategoryFactors.symm
        (R(jpush) ⋙ _root_.DerivedCategory.homologyFunctor B q)
    exact comparison_ofNatIso N c eopen
  let V := _root_.DerivedCategory.Q ⋙ F.rightAdjoint
  have hcostalk (q : ℤ) : IsIso (colimit.desc
      (N ⋙ V ⋙ _root_.DerivedCategory.homologyFunctor C q)
      ((V ⋙ _root_.DerivedCategory.homologyFunctor C q).mapCocone c)) := by
    have : IsIso (triangleComparison TT tc H q Triangle.π₁) :=
      triangleComparison_isIso TT tc hTT htc H (q - 1) q (by omega)
    change IsIso (colimit.desc
      (N ⋙ (_root_.DerivedCategory.Q ⋙ F.rightAdjoint ⋙ F ⋙
        _root_.DerivedCategory.homologyFunctor B q))
      ((_root_.DerivedCategory.Q ⋙ F.rightAdjoint ⋙ F ⋙
        _root_.DerivedCategory.homologyFunctor B q).mapCocone c)) at this
    let eclosed : _root_.DerivedCategory.Q ⋙ F.rightAdjoint ⋙ F ⋙
        _root_.DerivedCategory.homologyFunctor B q ≅
      V ⋙ _root_.DerivedCategory.homologyFunctor C q ⋙ ipush :=
      Functor.isoWhiskerLeft V (ipush.rightDerivedFunctorHomologyFunctorIso q).symm
    have hpush : IsIso (colimit.desc
        (N ⋙ V ⋙ _root_.DerivedCategory.homologyFunctor C q ⋙ ipush)
        ((V ⋙ _root_.DerivedCategory.homologyFunctor C q ⋙ ipush).mapCocone c)) :=
      comparison_ofNatIso N c eclosed
    have : ipush.IsLeftAdjoint :=
      (lowerStarClosedUpperShriekAdjunction M i j hij).isLeftAdjoint
    have hmap : IsIso (ipush.map (colimit.desc
        (N ⋙ V ⋙ _root_.DerivedCategory.homologyFunctor C q)
        ((V ⋙ _root_.DerivedCategory.homologyFunctor C q).mapCocone c))) := by
      have hcomp : IsIso (colimit.post
          (N ⋙ V ⋙ _root_.DerivedCategory.homologyFunctor C q) ipush ≫
          ipush.map (colimit.desc
            (N ⋙ V ⋙ _root_.DerivedCategory.homologyFunctor C q)
            ((V ⋙ _root_.DerivedCategory.homologyFunctor C q).mapCocone c))) := by
        rw [colimit.post_desc]
        exact hpush
      exact IsIso.of_isIso_comp_left
        (colimit.post (N ⋙ V ⋙ _root_.DerivedCategory.homologyFunctor C q) ipush) _
    exact isIso_of_reflects_iso _ ipush
  have hq : QuasiIso (colimit.desc (N ⋙ T) (T.mapCocone c)) := by
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let K := HomologicalComplex.homologyFunctor C (.up ℤ) q
    let ε : V ⋙ _root_.DerivedCategory.homologyFunctor C q ≅ T ⋙ K :=
      Functor.isoWhiskerRight e.symm (_root_.DerivedCategory.homologyFunctor C q) ≪≫
        Functor.isoWhiskerLeft T (_root_.DerivedCategory.homologyFunctorFactors C q)
    have : IsIso (colimit.desc (N ⋙ T ⋙ K) ((T ⋙ K).mapCocone c)) :=
      comparison_ofNatIso N c ε
    have hcomp : IsIso (colimit.post (N ⋙ T) K ≫
        K.map (colimit.desc (N ⋙ T) (T.mapCocone c))) := by
      rw [colimit.post_desc]
      exact this
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (colimit.post (N ⋙ T) K)
      (K.map (colimit.desc (N ⋙ T) (T.mapCocone c))) inferInstance hcomp
  unfold closedCostalkFilteredComparison
  have : IsIso (_root_.DerivedCategory.Q.map
      (colimit.desc (N ⋙ T) (T.mapCocone c))) :=
    (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  infer_instance

/-- Naturality in maps of diagrams and of their original cocones.
Source: Stacks Project, Tag 09XQ and its derived support triangle;
Bhatt–Scholze, Lemma 6.3.14 (closed factor)
(blueprint: lem-per-etale-closed-costalk-filtered-continuity).

Proof: Precompose the two chain-level maps with every colimit inclusion. The given
cocone equation and functoriality of T identify those composites, so the colimit universal
property gives equality. Apply Q and then the naturality of e at the cocone-apex map. -/
theorem closedCostalkFilteredComparison_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (e : T ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N N' : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (c : Cocone N) (c' : Cocone N') (α : N ⟶ N') (f : c.pt ⟶ c'.pt)
    (hf : ∀ j : J, c.ι.app j ≫ f = α.app j ≫ c'.ι.app j) :
    _root_.DerivedCategory.Q.map (colimMap (Functor.whiskerRight α T)) ≫
        closedCostalkFilteredComparison A i T e N' c' =
      closedCostalkFilteredComparison A i T e N c ≫
        (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.map
          (_root_.DerivedCategory.Q.map f) := by
  have h : colimMap (Functor.whiskerRight α T) ≫
      colimit.desc (N' ⋙ T) (T.mapCocone c') =
      colimit.desc (N ⋙ T) (T.mapCocone c) ≫ T.map f := by
    apply colimit.hom_ext
    intro j
    simp only [ι_colimMap_assoc, Functor.whiskerRight_app, colimit.ι_desc,
      colimit.ι_desc_assoc, Functor.mapCocone_ι_app, ← T.map_comp]
    exact congrArg T.map (hf j).symm
  unfold closedCostalkFilteredComparison
  rw [← Category.assoc, ← _root_.DerivedCategory.Q.map_comp, h,
    _root_.DerivedCategory.Q.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using congrArg
    (fun g ↦ _root_.DerivedCategory.Q.map (colimit.desc (N ⋙ T) (T.mapCocone c)) ≫ g)
    (e.hom.naturality f)

/-- Independence under compatible quasi-isomorphic functorial representatives.
Source: Stacks Project, Tag 09XQ and its derived support triangle;
Bhatt–Scholze, Lemma 6.3.14 (closed factor)
(blueprint: lem-per-etale-closed-costalk-filtered-continuity).

Proof: Exact filtered colimits commute with homology, so the colimit of the
objectwise quasi-isomorphism τ is a quasi-isomorphism and Q inverts it. The cocone
compatibility ht compares the chain-level universal maps. The equation he identifies
their localized target maps. Thus the two comparisons agree after the specified canonical
identification; the assertion also applies to zigzags by composition and inversion. -/
theorem closedCostalkFilteredComparison_representative_independence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T T' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (e : T ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint)
    (e' : T' ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (c : Cocone N) (τ : N ⋙ T ⟶ N ⋙ T')
    (t : T.obj c.pt ⟶ T'.obj c.pt) (hτ : ∀ j : J, QuasiIso (τ.app j))
    (hτe : ∀ j : J, _root_.DerivedCategory.Q.map (τ.app j) ≫
      e'.hom.app (N.obj j) = e.hom.app (N.obj j))
    (ht : ∀ j : J, T.map (c.ι.app j) ≫ t = τ.app j ≫ T'.map (c.ι.app j))
    (he : _root_.DerivedCategory.Q.map t ≫ e'.hom.app c.pt = e.hom.app c.pt) :
    IsIso (_root_.DerivedCategory.Q.map (colimMap τ)) ∧
    closedCostalkFilteredComparison A i T e N c =
      _root_.DerivedCategory.Q.map (colimMap τ) ≫
        closedCostalkFilteredComparison A i T' e' N c := by
  have _ := hτe
  have hq : QuasiIso (colimMap τ) :=
    (HomologicalComplex.quasiIso
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).colimMap τ hτ
  have h : colimMap τ ≫ colimit.desc (N ⋙ T') (T'.mapCocone c) =
      colimit.desc (N ⋙ T) (T.mapCocone c) ≫ t := by
    apply colimit.hom_ext
    intro j
    simp only [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc,
      Functor.mapCocone_ι_app]
    exact (ht j).symm
  refine ⟨(_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq, ?_⟩
  unfold closedCostalkFilteredComparison
  rw [← Category.assoc, ← _root_.DerivedCategory.Q.map_comp, h,
    _root_.DerivedCategory.Q.map_comp, Category.assoc, he]

end AlgebraicGeometry.Etale
