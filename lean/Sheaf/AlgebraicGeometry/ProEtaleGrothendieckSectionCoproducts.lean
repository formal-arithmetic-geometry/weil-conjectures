/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtaleQcqsSiteLimits
import Sheaf.CategoryTheory.FiniteHypercoverColimits
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Sheaf.CategoryTheory.CategoricalFiniteCechCriterion
import Sheaf.CategoryTheory.CategoricalInjectiveCechExactness
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Coproducts of Grothendieck-valued pro-etale sheaf sections on qcqs objects -/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private theorem finite_affine_cover_refinement (X : Scheme.{u}) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] (S : Sieve W) (hS : S ∈ topology X W) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (V : I → X.ProEt) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ topology X W ∧ (∀ i, S (f i)) ∧ (∀ i, IsAffine (V i).left) := by
  classical
  have : (precoverage X).IsStableUnderComposition := by
    dsimp [precoverage]
    infer_instance
  have : (precoverage X).HasIsos := by dsimp [precoverage]; infer_instance
  have : (precoverage X).IsStableUnderBaseChange := by
    dsimp [precoverage]
    infer_instance
  obtain ⟨T, hT, hTS⟩ :=
    (precoverage X).mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  let E := T.preZeroHypercover
  let F := ProEt.forget X ⋙ Over.forget X
  let E' := E.map F
  have hE' : E'.presieve₀ ∈ Scheme.proetalePrecoverage W.left := by
    have he : E'.presieve₀ = Presieve.map F T := by
      dsimp only [E']
      rw [PreZeroHypercover.presieve₀_map]
      exact congrArg (Presieve.map F) T.presieve₀_preZeroHypercover
    rw [he]
    exact hT
  let U : W.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨E', hE'.2⟩
  let : QuasiCompactCover U.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE'.1
  obtain ⟨A, r, hfin, _⟩ := QuasiCompactCover.exists_hom U
  let := hfin
  have : Finite A.cover.I₀ := hfin
  have (i : A.cover.I₀) : QuasiCompact (A.cover.f i) := by
    apply quasiCompact_of_compactSpace
  have : QuasiCompactCover A.cover.toPreZeroHypercover := QuasiCompactCover.of_finite
  have (i : A.I₀) : WeaklyEtale (A.f i) := A.cover.map_prop i
  let V : A.I₀ → X.ProEt := fun i ↦ ProEt.mk (A.f i ≫ W.hom)
  let f : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (A.f i) (by rfl)
  refine ⟨A.I₀, hfin, V, f, ?_, ?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    change Presieve.map F (Presieve.ofArrows V f) ∈ Scheme.proetalePrecoverage W.left
    rw [Presieve.map_ofArrows]
    change A.cover.presieve₀ ∈ Scheme.proetalePrecoverage W.left
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr inferInstance, A.cover.mem₀⟩
  · intro i
    let e := r.s₀ i
    let g : V i ⟶ E.X e := MorphismProperty.Over.homMk (r.h₀ i) (by
      change r.h₀ i ≫ (E.X e).hom = A.f i ≫ W.hom
      have he : r.h₀ i ≫ (E.f e).left = A.f i := r.w₀ i
      rw [← he, Category.assoc]
      congr 1
      simp)
    have hg : g ≫ E.f e = f i := by
      apply (ProEt.forget X).map_injective
      apply Over.OverMorphism.ext
      exact r.w₀ i
    rw [← hg]
    exact S.downward_closed (hTS _ _ e.2) g
  · intro i
    change IsAffine (Spec (A.X i))
    infer_instance

private instance qcqs_full (X : Scheme.{u}) : (qcqsInclusion X).Full :=
  inferInstanceAs (qcqsObjects X).ι.Full

private instance qcqs_faithful (X : Scheme.{u}) : (qcqsInclusion X).Faithful :=
  inferInstanceAs (qcqsObjects X).ι.Faithful

private def qcqsTopology (X : Scheme.{u}) : GrothendieckTopology (Qcqs X) :=
  (qcqsInclusion X).restrictedTopology (topology X)

private instance qcqs_coverDense (X : Scheme.{u}) :
    (qcqsInclusion X).IsCoverDense (topology X) where
  is_cover V := by
    let C := V.left.affineOpenCover
    let U (i : C.I₀) : X.ProEt := ProEt.mk (C.f i ≫ V.hom)
    have (i : C.I₀) : IsAffine (U i).left := by
      change IsAffine (Spec (C.X i))
      infer_instance
    let f (i : C.I₀) : U i ⟶ V := MorphismProperty.Over.homMk (C.f i)
    have hcover : Sieve.ofArrows U f ∈ topology X V := by
      apply Precoverage.generate_mem_toGrothendieck
      change (Presieve.ofArrows U f).map (ProEt.forget X ⋙ Over.forget X) ∈
        proetalePrecoverage V.left
      rw [Presieve.map_ofArrows]
      exact (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale)) _
        C.openCover.mem₀
    apply (topology X).superset_covering _ hcover
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    let T : Qcqs X := ⟨U i, inferInstance, inferInstance⟩
    exact Presieve.in_coverByImage (qcqsInclusion X) (Y := T) (f i)

private instance qcqs_finiteHypercovers (X : Scheme.{u}) :
    (qcqsTopology X).finiteOneHypercover.{u, u + 1, u + 1}.IsGenerating where
  le {T} S hS := by
    obtain ⟨hp, P, hP, hlim, hscheme, hmap, hslice, hfinite, hadjoin⟩ := qcqs_site_limits X
    let : HasPullbacks (Qcqs X) := hp
    have hS' : S.functorPushforward (qcqsInclusion X) ∈ topology X T.obj :=
      Functor.mem_restrictedTopology_iff.mp hS
    let : CompactSpace T.obj.left := T.property.1
    let : QuasiSeparatedSpace T.obj.left := T.property.2
    obtain ⟨I, hI, V, f, hcov, hf, haff⟩ :=
      finite_affine_cover_refinement X T.obj _ hS'
    let : Finite I := hI
    let W (i : I) : Qcqs X :=
      have : IsAffine (V i).left := haff i
      ⟨V i, inferInstance, inferInstance⟩
    let g (i : I) : W i ⟶ T := (qcqsInclusion X).preimage (f i)
    have hg (i : I) : S (g i) := by
      apply (Sieve.mem_functorPushforward_iff_of_full_of_faithful
        (qcqsInclusion X) S (g i)).1
      simpa [g] using hf i
    have hcover : Sieve.ofArrows W g ∈ qcqsTopology X T := by
      apply Functor.mem_restrictedTopology_iff.mpr
      rw [Sieve.functorPushforward_ofArrows]
      simp only [g, Functor.map_preimage]
      simpa only [W, qcqsInclusion, ObjectProperty.ι_obj] using hcov
    let E₀ : PreZeroHypercover T := { I₀ := I, X := W, f := g }
    let : E₀.Finite := ⟨hI⟩
    let E : (qcqsTopology X).OneHypercover T :=
      .mk' E₀.toPreOneHypercover hcover (by simp)
    refine ⟨E, ?_, ?_⟩
    · change E₀.toPreOneHypercover.Finite
      infer_instance
    · rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
        Presieve.ofArrows_le_iff]
      exact hg

/-- Sections on a qcqs pro-etale object commute with coproducts with coefficients in
any Grothendieck abelian category. Source: Stacks Project, Tag 0738 and the qcqs
subsite in the proof of Tag 09A1.

Proof: The qcqs full subsite is cover dense, since affine open covers factor through
it. Every covering sieve on this subsite contains a finite affine refinement; pairwise
pullbacks stay qcqs. Consequently finite one-hypercovers generate its topology.
Restriction along the dense inclusion is an equivalence of sheaf categories. The
coproduct functor in a Grothendieck abelian category is exact and therefore preserves
finite limits. The finite-hypercover pointwise-colimit theorem shows that the sheaf
inclusion on the subsite preserves coproducts. Compose restriction, this inclusion,
and evaluation at the given qcqs object. This composite is precisely the original
section functor. All three factors preserve coproducts, including the empty one. -/
private theorem qcqs_evaluation_preservesCoproducts
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left] (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (sheafToPresheaf (topology X) A ⋙ (CategoryTheory.evaluation X.ProEtᵒᵖ A).obj (op V)) := by
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasLimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasLimits A
  let : HasLimitsOfSize.{u, u + 1} A :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let J := qcqsTopology X
  let G := qcqsInclusion X
  let : G.IsDenseSubsite J (topology X) := by
    dsimp [G, J, qcqsTopology]
    infer_instance
  let R := G.sheafPushforwardContinuous A J (topology X)
  let : ∀ W, HasLimitsOfShape (StructuredArrow W G.op) A := fun _ ↦ inferInstance
  let : R.IsEquivalence := by
    change (G.sheafPushforwardContinuous A J (topology X)).IsEquivalence
    infer_instance
  let : PreservesColimitsOfShape (Discrete I) (sheafToPresheaf J A) :=
    sheafToPresheaf_preservesColimits_of_finiteHypercovers J
  let W : Qcqs X := ⟨V, inferInstance, inferInstance⟩
  change PreservesColimitsOfShape (Discrete I)
    ((R ⋙ sheafToPresheaf J A) ⋙ (CategoryTheory.evaluation (Qcqs X)ᵒᵖ A).obj (op W))
  infer_instance

variable {X : Scheme.{u}}

private lemma compactSpace_and_quasiSeparatedSpace_of_iso {A B : X.ProEt} (e : A ≅ B)
    (h : CompactSpace A.left ∧ QuasiSeparatedSpace A.left) :
    CompactSpace B.left ∧ QuasiSeparatedSpace B.left := by
  let φ := TopCat.homeoOfIso
    (Scheme.forgetToTop.mapIso ((ProEt.forget X ⋙ Over.forget X).mapIso e))
  exact ⟨@Homeomorph.compactSpace _ _ _ _ h.1 φ, (quasiSeparatedSpace_congr φ).1 h.2⟩

/-- A fibre product of weakly étale `X`-schemes with quasi-compact quasi-separated
underlying schemes over one with quasi-separated underlying scheme has quasi-compact
quasi-separated underlying scheme. -/
private lemma compactSpace_and_quasiSeparatedSpace_pullback {V A B : X.ProEt}
    (f : A ⟶ V) (g : B ⟶ V)
    [QuasiSeparatedSpace V.left] [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace B.left] [QuasiSeparatedSpace B.left] :
    CompactSpace (pullback f g).left ∧ QuasiSeparatedSpace (pullback f g).left := by
  let iso := PreservesPullback.iso (ProEt.forget X ⋙ Over.forget X) f g
  have : QuasiCompact f.left := quasiCompact_of_compactSpace _
  have : CompactSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) := inferInstance
  have : QuasiSeparatedSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f.left g.left)
  let φ := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso iso).symm
  exact ⟨@Homeomorph.compactSpace _ _ _ _ ‹_› φ, (quasiSeparatedSpace_congr φ).1 ‹_›⟩

/-- A finite product in `Over V` of weakly étale `X`-schemes with quasi-compact quasi-separated
underlying schemes has quasi-compact quasi-separated underlying scheme, if `V` has. -/
private lemma compactSpace_and_quasiSeparatedSpace_piObj {V : X.ProEt} [CompactSpace V.left]
    [QuasiSeparatedSpace V.left] {J : Type*} [Finite J] (U : J → Over V)
    (hU : ∀ j, CompactSpace (U j).left.left ∧ QuasiSeparatedSpace (U j).left.left) :
    CompactSpace (∏ᶜ U).left.left ∧ QuasiSeparatedSpace (∏ᶜ U).left.left := by
  let P : ObjectProperty (Over V) := fun A ↦
    CompactSpace A.left.left ∧ QuasiSeparatedSpace A.left.left
  have hiso {A B : Over V} (e : A ≅ B) (h : P A) : P B :=
    compactSpace_and_quasiSeparatedSpace_of_iso ((Over.forget V).mapIso e) h
  have : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := ⟨by
    rintro A ⟨h⟩
    have hA : IsTerminal A := (isLimitEquivIsTerminalOfIsEmpty _ _) h.isLimit
    exact hiso (Over.mkIdTerminal.uniqueUpToIso hA) ⟨‹_›, ‹_›⟩⟩
  have : P.IsClosedUnderBinaryProducts := ⟨by
    rintro A ⟨h⟩
    let e : A ≅ h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ :=
      h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫ HasLimit.isoOfNatIso (diagramIsoPair _)
    refine hiso e.symm ?_
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.left⟩
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.right⟩
    exact compactSpace_and_quasiSeparatedSpace_of_iso (Over.prodLeftIsoPullback _ _).symm
      (compactSpace_and_quasiSeparatedSpace_pullback _ _)⟩
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hU


private theorem finiteProductCocone_isColimit
    {A : Type u'} [Category.{u + 1} A] {K : Type} [Finite K]
    {D₀ : Type (u + 1)} [SmallCategory D₀]
    [HasColimitsOfShape D₀ A] [HasExactColimitsOfShape D₀ A]
    (D : K → D₀ ⥤ A) (P : D₀ ⥤ A) (π : ∀ k, P ⟶ D k)
    (hP : IsLimit (Fan.mk P π)) (c : ∀ k, Cocone (D k))
    (hc : ∀ k, IsColimit (c k))
    (t : Cocone P) (ρ : ∀ k, t.pt ⟶ (c k).pt)
    (hρ : IsLimit (Fan.mk t.pt ρ))
    (hcompat : ∀ j k, t.ι.app j ≫ ρ k = (π k).app j ≫ (c k).ι.app j) :
    Nonempty (IsColimit t) := by
  let e : Discrete.functor D ⋙ (colim : (D₀ ⥤ A) ⥤ A) ≅
      Discrete.functor (fun k ↦ (c k).pt) :=
    Discrete.natIso fun k ↦ (colimit.isColimit (D k.as)).coconePointUniqueUpToIso (hc k.as)
  let h := (IsLimit.postcomposeHomEquiv e _).symm (isLimitOfPreserves colim hP)
  let eP := h.conePointUniqueUpToIso hρ
  have hm : colimit.desc P t = eP.hom := by
    apply hρ.hom_ext
    intro k
    rw [IsLimit.conePointUniqueUpToIso_hom_comp]
    apply colimit.hom_ext
    intro j
    dsimp [e, Discrete.natIso]
    rw [colimit.ι_desc_assoc, ι_colimMap_assoc]
    erw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact hcompat j k.as
  have : IsIso (colimit.desc P t) := hm ▸ inferInstance
  change IsIso ((colimit.isColimit P).desc t) at this
  exact ⟨(colimit.isColimit P).ofPointIso⟩


private noncomputable def cech_coproduct_isColimit
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {I : Type (u + 1)} (H : I → Sheaf (topology X) A)
    {V : X.ProEt} {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      CompactSpace (Presheaf.cechNerveObj U y).left.left ∧
        QuasiSeparatedSpace (Presheaf.cechNerveObj U y).left.left) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
      IsGrothendieckAbelian.hasColimits _
    let T := sheafToPresheaf (topology X) A ⋙
      (Functor.whiskeringLeft (Over V)ᵒᵖ X.ProEtᵒᵖ A).obj (Over.forget V).op ⋙
      cechComplexFunctor U
    IsColimit (Cofan.mk (T.obj (∐ H)) (fun i ↦ T.map (Sigma.ι H i))) := by
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
    IsGrothendieckAbelian.hasColimits _
  dsimp only
  let T := sheafToPresheaf (topology X) A ⋙
    (Functor.whiskeringLeft (Over V)ᵒᵖ X.ProEtᵒᵖ A).obj (Over.forget V).op ⋙
    cechComplexFunctor U
  apply HomologicalComplex.isColimitOfEval
  intro k
  apply (isColimitMapCoconeCofanMkEquiv (HomologicalComplex.eval A (.up ℕ) k)
    (fun i ↦ T.obj (H i)) (fun i ↦ T.map (Sigma.ι H i))).2
  let K := Fin (k + 1) → Fin n
  let W (y : K) := (Presheaf.cechNerveObj U y).left
  let D (y : K) : Discrete I ⥤ A := Discrete.functor fun i ↦
    (H i).obj.obj (op (W y))
  let P : Discrete I ⥤ A := Discrete.functor fun i ↦ (T.obj (H i)).X k
  let π (y : K) : P ⟶ D y := Discrete.natTrans fun i ↦ Pi.π _ y
  have hP : IsLimit (Fan.mk P π) := by
    apply evaluationJointlyReflectsLimits
    intro i
    let e : Discrete.functor D ⋙ (CategoryTheory.evaluation (Discrete I) A).obj i ≅
        Discrete.functor (fun y : K ↦ (H i.as).obj.obj (op (W y))) :=
      Discrete.natIso fun _ ↦ Iso.refl _
    apply (IsLimit.postcomposeHomEquiv e _).1
    exact IsLimit.ofIsoLimit (productIsProduct (fun y : K ↦
      (H i.as).obj.obj (op (W y)))) (Cone.ext (Iso.refl _) (by intro y; simp [π, e]; rfl))
  let c (y : K) : Cocone (D y) := Cofan.mk ((∐ H).obj.obj (op (W y)))
    (fun i ↦ (Sigma.ι H i).hom.app (op (W y)))
  have hc (y : K) : IsColimit (c y) := by
    let : CompactSpace (W y).left := (hU k y).1
    let : QuasiSeparatedSpace (W y).left := (hU k y).2
    let E := sheafToPresheaf (topology X) A ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ A).obj (op (W y))
    let : PreservesColimitsOfShape (Discrete I) E :=
      qcqs_evaluation_preservesCoproducts A X (W y) I
    exact (isColimitMapCoconeCofanMkEquiv E H (Sigma.ι H)).1
      (isColimitOfPreserves E (coproductIsCoproduct H))
  let t : Cocone P := Cofan.mk ((T.obj (∐ H)).X k)
    (fun i ↦ (T.map (Sigma.ι H i)).f k)
  exact (finiteProductCocone_isColimit D P π hP c hc t
    (fun y ↦ Pi.π _ y) (productIsProduct _) (by
      intro i y
      dsimp [t, T, π, c, K, W]
      rw [cechComplexFunctor_map_f]
      erw [Limits.Pi.map_π]
      rfl)).some


private theorem finiteCech_coproduct_injective
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {I : Type (u + 1)} (H : I → Sheaf (topology X) A)
    (hH : ∀ i, Injective (H i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
      IsGrothendieckAbelian.hasColimits _
    Sheaf.finiteCechAcyclicOn
      (fun V : X.ProEt ↦ CompactSpace V.left ∧ QuasiSeparatedSpace V.left) (∐ H) := by
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasLimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasLimits A
  let : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
    IsGrothendieckAbelian.hasColimits _
  intro V hV n U hU hcover q
  let T := sheafToPresheaf (topology X) A ⋙
    (Functor.whiskeringLeft (Over V)ᵒᵖ X.ProEtᵒᵖ A).obj (Over.forget V).op ⋙
      cechComplexFunctor U
  let G := HomologicalComplex.homologyFunctor A (.up ℕ) (q + 1)
  have hz (i : I) : IsZero (G.obj (T.obj (H i))) := by
    have := hH i
    have : Injective (H i).obj :=
      (sheafificationAdjunction (topology X) A).map_injective (H i) inferInstance
    exact (Presheaf.exactAt_categoricalCech_of_injective (H i).obj U q).isZero_homology
  have hc := isColimitOfPreserves G (cech_coproduct_isColimit A H U hU)
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply hc.hom_ext
  intro i
  exact (hz i.as).eq_of_src _ _

private theorem qcqs_finite_cech_covers (V : X.ProEt)
    (hV : CompactSpace V.left ∧ QuasiSeparatedSpace V.left)
    (S : Sieve V) (hS : S ∈ topology X V) :
    ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
        CompactSpace (Presheaf.cechNerveObj U y).left.left ∧
          QuasiSeparatedSpace (Presheaf.cechNerveObj U y).left.left) ∧
      (∀ a, S (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ topology X V := by
  classical
  let : CompactSpace V.left := hV.1
  let : QuasiSeparatedSpace V.left := hV.2
  obtain ⟨I, hI, W, f, hcov, hf, haff⟩ := finite_affine_cover_refinement X V S hS
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let e := (Fintype.equivFin I).symm
  let U : Fin (Fintype.card I) → Over V := fun a ↦ Over.mk (f (e a))
  refine ⟨Fintype.card I, U, ?_, fun a ↦ hf (e a), ?_⟩
  · intro k y
    apply compactSpace_and_quasiSeparatedSpace_piObj
    intro l
    change CompactSpace (W (e (y l))).left ∧
      QuasiSeparatedSpace (W (e (y l))).left
    have : IsAffine (W (e (y l))).left := haff _
    exact ⟨inferInstance, inferInstance⟩
  · change Sieve.ofArrows (W ∘ e) (fun a ↦ f (e a)) ∈ topology X V
    simpa only [Sieve.ofArrows,
      Presieve.ofArrows_comp_eq_of_surjective f e.surjective] using hcov


private instance qcqs_denseSubsite (Y : Scheme.{u}) :
    (qcqsInclusion Y).IsDenseSubsite (qcqsTopology Y) (topology Y) := by
  dsimp [qcqsTopology]
  infer_instance

private instance qcqs_restriction_equivalence
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (Y : Scheme.{u}) :
    ((qcqsInclusion Y).sheafPushforwardContinuous A (qcqsTopology Y)
      (topology Y)).IsEquivalence := by
  let : HasLimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasLimits A
  let : HasLimitsOfSize.{u, u + 1} A :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let : (qcqsInclusion Y).IsDenseSubsite (qcqsTopology Y) (topology Y) := by
    dsimp [qcqsTopology]
    infer_instance
  let : ∀ W, HasLimitsOfShape (StructuredArrow W (qcqsInclusion Y).op) A :=
    fun _ ↦ inferInstance
  infer_instance

private theorem isIso_of_qcqs_evaluation
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Y : Scheme.{u}}
    {F G : Sheaf (topology Y) A} (φ : F ⟶ G)
    (hφ : ∀ V : Y.ProEt, CompactSpace V.left → QuasiSeparatedSpace V.left →
      IsIso (φ.hom.app (op V))) : IsIso φ := by
  let R := (qcqsInclusion Y).sheafPushforwardContinuous A (qcqsTopology Y) (topology Y)
  let T := R ⋙ sheafToPresheaf (qcqsTopology Y) A
  have h (V : (Qcqs Y)ᵒᵖ) : IsIso ((T.map φ).app V) :=
    hφ V.unop.obj V.unop.property.1 V.unop.property.2
  have : IsIso (T.map φ) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso φ T

private theorem epi_of_qcqs_evaluation
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Y : Scheme.{u}}
    {F G : Sheaf (topology Y) A} (φ : F ⟶ G)
    (hφ : ∀ V : Y.ProEt, CompactSpace V.left → QuasiSeparatedSpace V.left →
      Epi (φ.hom.app (op V))) : Epi φ := by
  let R := (qcqsInclusion Y).sheafPushforwardContinuous A (qcqsTopology Y) (topology Y)
  let T := R ⋙ sheafToPresheaf (qcqsTopology Y) A
  have h (V : (Qcqs Y)ᵒᵖ) : Epi ((T.map φ).app V) :=
    hφ V.unop.obj V.unop.property.1 V.unop.property.2
  exact T.epi_of_epi_map (NatTrans.epi_of_epi_app _)

private theorem qcqs_baseChange {Y : Scheme.{u}} (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p] (V : Y.ProEt)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left] :
    let W := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj V
    CompactSpace W.left ∧ QuasiSeparatedSpace W.left := by
  let : CompactSpace ((𝟭 Scheme).obj V.left) := ‹CompactSpace V.left›
  let : QuasiSeparatedSpace ((𝟭 Scheme).obj V.left) := ‹QuasiSeparatedSpace V.left›
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom p),
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst V.hom p)⟩

private theorem lowerStar_preservesCoproducts
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Y : Scheme.{u}} (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p] (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) (ProEtale.lowerStar A p) := by
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
    IsGrothendieckAbelian.hasColimits _
  let : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology Y) A) :=
    IsGrothendieckAbelian.hasColimits _
  let F := ProEtale.lowerStar A p
  constructor
  intro K
  have : IsIso (colimit.post K F) := by
    apply isIso_of_qcqs_evaluation A
    intro V hc hs
    let : CompactSpace V.left := hc
    let : QuasiSeparatedSpace V.left := hs
    let W := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj V
    let : CompactSpace W.left := (qcqs_baseChange p V).1
    let : QuasiSeparatedSpace W.left := (qcqs_baseChange p V).2
    let E := sheafToPresheaf (topology Y) A ⋙
      (CategoryTheory.evaluation Y.ProEtᵒᵖ A).obj (op V)
    let : PreservesColimitsOfShape (Discrete I) E :=
      qcqs_evaluation_preservesCoproducts A Y V I
    let : PreservesColimitsOfShape (Discrete I) (F ⋙ E) := by
      change PreservesColimitsOfShape (Discrete I)
        (sheafToPresheaf (topology X) A ⋙
          (CategoryTheory.evaluation X.ProEtᵒᵖ A).obj (op W))
      exact qcqs_evaluation_preservesCoproducts A X W I
    have hcomp : colimit.post (K ⋙ F) E ≫ E.map (colimit.post K F) =
        colimit.post K (F ⋙ E) := by
      apply colimit.hom_ext
      intro i
      simp
    have : IsIso (colimit.post (K ⋙ F) E ≫ E.map (colimit.post K F)) := by
      rw [hcomp]
      infer_instance
    exact (isIso_comp_left_iff (colimit.post (K ⋙ F) E)
      (E.map (colimit.post K F))).1 inferInstance
  exact preservesColimit_of_isIso_post F K


private theorem injectiveSum_eval_acyclic
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {I : Type (u + 1)} (H : I → Sheaf (topology X) A)
    (hH : ∀ i, Injective (H i)) (V : X.ProEt)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left] :
    letI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
      IsGrothendieckAbelian.hasColimits _
    (sheafToPresheaf (topology X) A ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ A).obj (op V)).rightAcyclic (∐ H) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
    IsGrothendieckAbelian.hasColimits _
  intro q
  exact Sheaf.isZero_rightDerived_eval_of_finiteCech
    (fun V : X.ProEt ↦ CompactSpace V.left ∧ QuasiSeparatedSpace V.left)
    qcqs_finite_cech_covers (∐ H) (finiteCech_coproduct_injective A H hH)
    V ⟨inferInstance, inferInstance⟩ q

private theorem lowerStar_injectiveSum_acyclic
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Y : Scheme.{u}} (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    {I : Type (u + 1)} (H : I → Sheaf (topology X) A)
    (hH : ∀ i, Injective (H i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
      IsGrothendieckAbelian.hasColimits _
    (ProEtale.lowerStar A p).rightAcyclic (∐ H) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
    IsGrothendieckAbelian.hasColimits _
  let P : ObjectProperty (Sheaf (topology X) A) := fun F ↦
    ∀ (V : X.ProEt), CompactSpace V.left → QuasiSeparatedSpace V.left →
      (sheafToPresheaf (topology X) A ⋙
        (CategoryTheory.evaluation X.ProEtᵒᵖ A).obj (op V)).rightAcyclic F
  apply Functor.rightAcyclic_of_epi_map_g (ProEtale.lowerStar A p) P
  · intro J hJ V hc hs
    exact Functor.rightAcyclic_of_injective J
  · intro S hS h₁ h₂ V hc hs
    exact hS.rightAcyclic_X₃ (h₁ V hc hs) (h₂ V hc hs)
  · intro S hS h₁
    apply epi_of_qcqs_evaluation A
    intro V hc hs
    let : CompactSpace V.left := hc
    let : QuasiSeparatedSpace V.left := hs
    let W := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj V
    let E := sheafToPresheaf (topology X) A ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ A).obj (op W)
    exact (hS.map_of_rightAcyclic (F := E)
      (h₁ W (qcqs_baseChange p V).1 (qcqs_baseChange p V).2)).epi_g
  · intro V hc hs
    let : CompactSpace V.left := hc
    let : QuasiSeparatedSpace V.left := hs
    exact injectiveSum_eval_acyclic A H hH V

/-- Quasi-compact quasi-separated direct image preserves coproducts, and sums of
injective sheaves are acyclic for it. Source: Stacks Project, Tags 0738 and 03F9;
the qcqs subsite argument in Tag 09A1;
and the direct-sum conclusion of Tag 09A3 (here proved for Grothendieck coefficients).
(blueprint: stage3-proetale-grothendieck-coproduct-acyclicity).

Proof: Work on the cover-dense qcqs full subsite. Every covering sieve there admits a
finite affine refinement, and finite limits remain qcqs. Exact coproducts of coefficient
objects therefore compute sheaf coproducts on this subsite. This gives coproduct
preservation of evaluation on qcqs objects. Base change by the given morphism stays
qcqs, so evaluation detects that direct image preserves coproducts. For acyclicity,
the finite Cech complex of a sum of injective sheaves is the degreewise coproduct of
the individual Cech complexes: each degree is a finite product of qcqs section
functors. Each individual complex is positively exact, and exact coproducts preserve
this. The finite Cech criterion gives acyclicity of evaluation on every qcqs object.
Finally apply dimension shifting to direct image: this class contains injectives,
is closed under cokernels of monomorphisms, and makes direct image right exact on
short exact sequences, as can be checked on the qcqs subsite of the target. -/
theorem lowerStar_coproducts_and_injectiveSum_acyclic
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Y : Scheme.{u}} (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p] (I : Type (u + 1)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) A) :=
      IsGrothendieckAbelian.hasColimits _
    PreservesColimitsOfShape (Discrete I) (ProEtale.lowerStar A p) ∧
      ∀ H : I → Sheaf (topology X) A, (∀ i, Injective (H i)) →
        (ProEtale.lowerStar A p).rightAcyclic (∐ H) := by
  exact ⟨lowerStar_preservesCoproducts A p I, fun H hH ↦
    lowerStar_injectiveSum_acyclic A p H hH⟩

end AlgebraicGeometry.Scheme.ProEt
