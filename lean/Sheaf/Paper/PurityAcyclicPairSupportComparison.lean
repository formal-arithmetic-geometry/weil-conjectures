/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneSectionData
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! # Localization of a cohomologically trivial line pair

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4;
Stacks, Tags 03F3 and 099W; blueprint sk-prop-a1-kummer, localization and site comparison.
(blueprint: lem-pur-acyclic-pair-support-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

private theorem injective_module_restriction
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    (I : Sheaf J (ModuleCat.{u + 1} A)) [Injective I]
    {W V : C} (j : W ⟶ V) [Mono j] : Function.Surjective (I.obj.map j.op) := by
  let P (T : C) := uliftYoneda.{u + 1}.obj T ⋙ ModuleCat.free A
  let a : P W ⟶ P V :=
    Functor.whiskerRight (uliftYoneda.{u + 1}.map j) (ModuleCat.free A)
  have ha : Mono a := by
    have (T : Cᵒᵖ) : Mono (a.app T) := by
      apply (ModuleCat.mono_iff_injective _).mpr
      change Function.Injective (Finsupp.mapDomain (fun f : ULift.{u + 1} (T.unop ⟶ W) ↦
        ULift.up (f.down ≫ j)))
      apply Finsupp.mapDomain_injective
      intro f g h
      apply ULift.ext
      exact (cancel_mono j).mp (congrArg ULift.down h)
    exact NatTrans.mono_of_mono_app a
  have : Injective I.obj := (sheafificationAdjunction J (ModuleCat.{u + 1} A)).map_injective
    I inferInstance
  intro x
  let b : P W ⟶ I.obj := {
    app := fun T ↦ ModuleCat.freeDesc (↾fun f : ULift.{u + 1} (T.unop ⟶ W) ↦
      I.obj.map f.down.op x)
    naturality := by
      intro T T' f
      apply ModuleCat.free_hom_ext
      intro g
      change (ModuleCat.freeDesc _)
        ((ModuleCat.free A).map _ (ModuleCat.freeMk g)) = _
      simp only [ModuleCat.free_map_apply, ConcreteCategory.comp_apply,
        ModuleCat.freeDesc_apply]
      change I.obj.map (f.unop ≫ g.down).op x =
        I.obj.map f (I.obj.map g.down.op x)
      rw [op_comp, I.obj.map_comp]
      rfl }
  obtain ⟨g, hg⟩ := Injective.factors b a
  refine ⟨g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V))), ?_⟩
  have hn := congrArg (fun h ↦ h (ModuleCat.freeMk (ULift.up (𝟙 V))))
    (g.naturality j.op)
  have hf := congrArg (fun h ↦ h.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W)))) hg
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hf
  simp only [ConcreteCategory.comp_apply] at hn
  have he : (P V).map j.op (ModuleCat.freeMk (ULift.up (𝟙 V))) =
      a.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W))) := by
    change (ModuleCat.free A).map _ _ = (ModuleCat.free A).map _ _
    simp only [ModuleCat.free_map_apply]
    change ModuleCat.freeMk (ULift.up (j ≫ 𝟙 V)) =
      ModuleCat.freeMk (ULift.up (𝟙 W ≫ j))
    simp
  rw [he] at hn
  have hh := hn.symm.trans hf
  change _ = (ModuleCat.freeDesc _) (ModuleCat.freeMk _) at hh
  rw [ModuleCat.freeDesc_apply] at hh
  simpa using hh

private theorem sectionComplex_shortExact
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    {W V : C} (j : W ⟶ V) [Mono j] {F : Sheaf J (ModuleCat.{u + 1} A)}
    (I : InjectiveResolution F) : (sectionComplex J A j I.cocomplex).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel ((I.cocomplex.X n).obj.map j.op))
  · change Mono (kernel.ι ((I.cocomplex.X n).obj.map j.op))
    infer_instance
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact injective_module_restriction J A (I.cocomplex.X n) j

private def resolutionBoundary
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {W V : C} (j : W ⟶ V) [Mono j] {F : Sheaf J (ModuleCat.{u + 1} A)}
    (I : InjectiveResolution F) :=
  (I.isoRightDerivedObj (sections J A W) 1).hom ≫
    (sectionComplex_shortExact J A j I).δ 1 2 rfl ≫
    (I.isoRightDerivedObj (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv

set_option backward.isDefEq.respectTransparency false in
private theorem resolutionBoundary_eq
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {W V : C} (j : W ⟶ V) [Mono j] {F : Sheaf J (ModuleCat.{u + 1} A)}
    (I K : InjectiveResolution F) : resolutionBoundary J A j I =
      resolutionBoundary J A j K := by
  let f := InjectiveResolution.desc (𝟙 F) K I
  let φ : sectionComplex J A j I.cocomplex ⟶ sectionComplex J A j K.cocomplex := {
    τ₁ := ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
      (.up ℕ)).map f
    τ₂ := ((sections J A V).mapHomologicalComplex (.up ℕ)).map f
    τ₃ := ((sections J A W).mapHomologicalComplex (.up ℕ)).map f
    comm₁₂ := NatTrans.mapHomologicalComplex_naturality
      (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j) f
    comm₂₃ := NatTrans.mapHomologicalComplex_naturality
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) f }
  have hd := HomologicalComplex.HomologySequence.δ_naturality φ
    (sectionComplex_shortExact J A j I) (sectionComplex_shortExact J A j K) 1 2 rfl
  have hu := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 F) I K f
    (InjectiveResolution.desc_commutes_zero (𝟙 F) K I) (sections J A W) 1
  have hz := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 F) I K f
    (InjectiveResolution.desc_commutes_zero (𝟙 F) K I)
      (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at hu hz
  change (I.isoRightDerivedObj (sections J A W) 1).hom ≫
      (sectionComplex_shortExact J A j I).δ 1 2 rfl ≫
      (I.isoRightDerivedObj (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv =
    (K.isoRightDerivedObj (sections J A W) 1).hom ≫
      (sectionComplex_shortExact J A j K).δ 1 2 rfl ≫
      (K.isoRightDerivedObj (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv
  rw [hz, hu]
  dsimp only [φ, Functor.comp_map] at hd
  simpa only [Category.assoc, Functor.comp_map, HomologicalComplex.homologyFunctor_map]
    using congrArg
    (fun t ↦ (I.isoRightDerivedObj (sections J A W) 1).hom ≫ t ≫
      (K.isoRightDerivedObj (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv)
    hd

private theorem exists_boundary
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {W V : C} (j : W ⟶ V) [Mono j] (F : Sheaf J (ModuleCat.{u + 1} A)) :
    ∃ δ, IsBoundary J A j F δ := by
  refine ⟨resolutionBoundary J A j (injectiveResolution F), ?_⟩
  intro I
  exact ⟨sectionComplex_shortExact J A j I,
    resolutionBoundary_eq J A j (injectiveResolution F) I⟩

private theorem boundary_isIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {W V : C} (j : W ⟶ V) (F : Sheaf J (ModuleCat.{u + 1} A))
    (δ : ((sections J A W).rightDerived 1).obj F ⟶
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived 2).obj F)
    (hδ : IsBoundary J A j F δ)
    (h₁ : IsZero (((sections J A V).rightDerived 1).obj F))
    (h₂ : IsZero (((sections J A V).rightDerived 2).obj F)) : IsIso δ := by
  let I := injectiveResolution F
  obtain ⟨hI, he⟩ := hδ I
  have h₁' : IsZero ((sectionComplex J A j I.cocomplex).X₂.homology 1) :=
    h₁.of_iso (I.isoRightDerivedObj (sections J A V) 1).symm
  have h₂' : IsZero ((sectionComplex J A j I.cocomplex).X₂.homology 2) :=
    h₂.of_iso (I.isoRightDerivedObj (sections J A V) 2).symm
  have := hI.isIso_δ 1 2 rfl h₁' h₂'
  rw [he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem localization_consequences
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {W V : C} (j : W ⟶ V) [Mono j] (F : Sheaf J (ModuleCat.{u + 1} A))
    (hV : ∀ q : ℕ, 0 < q → IsZero (((sections J A V).rightDerived q).obj F))
    (hW : ∀ q : ℕ, 2 ≤ q → IsZero (((sections J A W).rightDerived q).obj F))
    (hres : IsIso ((NatTrans.rightDerived
      (F := sections J A V) (G := sections J A W)
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) 0).app F)) :
    ∃ δ, IsBoundary J A j F δ ∧ IsIso δ ∧
      ∀ q : ℕ, q ≠ 2 → IsZero
        (((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived q).obj F) := by
  obtain ⟨δ, hδ⟩ := exists_boundary J A j F
  refine ⟨δ, hδ, boundary_isIso J A j F δ hδ (hV 1 (by omega))
    (hV 2 (by omega)), ?_⟩
  let I := injectiveResolution F
  let S := sectionComplex J A j I.cocomplex
  have hS : S.ShortExact := sectionComplex_shortExact J A j I
  have hV' (q : ℕ) (hq : 0 < q) : IsZero (S.X₂.homology q) :=
    (hV q hq).of_iso (I.isoRightDerivedObj (sections J A V) q).symm
  have hW' (q : ℕ) (hq : 2 ≤ q) : IsZero (S.X₃.homology q) :=
    (hW q hq).of_iso (I.isoRightDerivedObj (sections J A W) q).symm
  have hg : IsIso (HomologicalComplex.homologyMap S.g 0) := by
    have he : HomologicalComplex.homologyMap S.g 0 =
        (I.isoRightDerivedObj (sections J A V) 0).inv ≫
          (NatTrans.rightDerived (F := sections J A V) (G := sections J A W)
            ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) 0).app F ≫
          (I.isoRightDerivedObj (sections J A W) 0).hom := by
      rw [I.rightDerived_app_eq]
      simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
      rfl
    rw [he]
    infer_instance
  intro q hq
  apply IsZero.of_iso (e := I.isoRightDerivedObj
    (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) q)
  change IsZero (S.X₁.homology q)
  rcases q with _ | q
  · have : Mono (S.f.f 0) := by
      change Mono (kernel.ι _)
      infer_instance
    have : Mono (HomologicalComplex.homologyMap S.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0 (by
        intro i
        simp)
    have hf : HomologicalComplex.homologyMap S.f 0 = 0 :=
      (hS.homology_exact₂ 0).mono_g_iff.mp inferInstance
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (HomologicalComplex.homologyMap S.f 0)]
    simp only [Category.id_comp, Limits.zero_comp]
    exact hf
  · rcases q with _ | q
    · apply (hS.homology_exact₁ 0 1 rfl).isZero_X₂
      · apply (cancel_epi (HomologicalComplex.homologyMap S.g 0)).mp
        simp
      · exact (hV' 1 (by omega)).eq_of_tgt _ _
    · exact (hS.homology_exact₁ (q + 1) (q + 2) rfl).isZero_X₂
        ((hW' (q + 1) (by omega)).eq_of_src _ _)
        ((hV' (q + 2) (by omega)).eq_of_tgt _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_zero_isIso_iff
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {W V : C} (j : W ⟶ V) (M : Sheaf J (ModuleCat.{u + 1} A)) :
    IsIso ((NatTrans.rightDerived (F := sections J A V) (G := sections J A W)
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) 0).app M) ↔
      IsIso (M.obj.map j.op) := by
  let F := sections J A V
  let G := sections J A W
  let α : F ⟶ G := (sheafSections J (ModuleCat.{u + 1} A)).map j.op
  let P := injectiveResolution M
  let φ := (NatTrans.mapHomologicalComplex α (.up ℕ)).app P.cocomplex
  have hc : α.app M ≫ P.toRightDerivedZero' G =
      P.toRightDerivedZero' F ≫ HomologicalComplex.cyclesMap φ 0 := by
    apply (cancel_mono (HomologicalComplex.iCycles _ 0)).mp
    rw [Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      Category.assoc, HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    exact (α.naturality (P.ι.f 0)).symm
  have h : α.app M ≫ G.toRightDerivedZero.app M =
      F.toRightDerivedZero.app M ≫ (NatTrans.rightDerived α 0).app M := by
    rw [P.toRightDerivedZero_eq F, P.toRightDerivedZero_eq G,
      P.rightDerived_app_eq α 0]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change α.app M ≫ P.toRightDerivedZero' G ≫
        ((G.mapHomologicalComplex _).obj P.cocomplex).homologyπ 0 ≫
          (P.isoRightDerivedObj G 0).inv =
      P.toRightDerivedZero' F ≫
        ((F.mapHomologicalComplex _).obj P.cocomplex).homologyπ 0 ≫
          HomologicalComplex.homologyMap φ 0 ≫ (P.isoRightDerivedObj G 0).inv
    rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc, hc,
      Category.assoc]
  change IsIso ((NatTrans.rightDerived α 0).app M) ↔ IsIso (α.app M)
  rw [← isIso_comp_left_iff (F.toRightDerivedZero.app M), ← h,
    isIso_comp_right_iff]

private theorem comparisonSections_isIso
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale) :
    IsIso (comparisonSections A X W) := by
  have := ProEtale.isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} A) X
  have (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      IsIso ((comparisonSections A X W).app F) := by
    change IsIso (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app F).hom.app
      (op W))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private theorem comparison_sections_acyclic
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) [Injective I] :
    (sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W)).rightAcyclic
      (proCoefficient A X I) := by
  have : AlgebraicGeometry.Etale W.hom := W.prop
  have : Injective ((Etale.upperStar (ModuleCat.{u + 1} A) W.hom).obj I) :=
    Etale.injective_upperStar_obj_of_etale' (ModuleCat.{u + 1} A) W.hom I
  intro q
  apply ProEtale.isZero_rightDerived_sectionsFunctor_of_upperStar
    (ModuleCat.{u + 1} A) ((Scheme.toProEt X).obj W)
  have h := ProEtale.isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj
    (ModuleCat.{u + 1} A) W.left
    ((Etale.upperStar (ModuleCat.{u + 1} A) W.hom).obj I) (q + 1)
    (Functor.isZero_rightDerived_obj_injective_succ _ q _)
  exact h.of_iso
    (((ProEtale.globalSectionsFunctor (ModuleCat.{u + 1} A) W.left).rightDerived (q + 1)).mapIso
      ((ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) W.hom).app I))

private theorem comparisonCohomology_isIso
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale) (q : ℕ) :
    IsIso (comparisonCohomology A X W q) := by
  have := comparisonSections_isIso A X W
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange (comparisonSections A X W)) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (asIso (comparisonSections A X W)) (comparison_sections_acyclic A X W)
  unfold comparisonCohomology
  dsimp only [Functor.rightDerivedBaseChange]
  infer_instance

/-- The normalized localization boundaries and comparison for an acyclic open pair.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 09XP;
blueprint rank-one local calculation, Steps 4 and 7
(blueprint: lem-pur-acyclic-pair-support-comparison).

Proof: On either site the restriction of an injective module sheaf along the open
monomorphism is surjective: sections are represented by free module sheafifications,
and their monomorphism allows injectivity to extend any section. Thus the three section
complexes of every injective resolution form the kernel short exact sequence. Its snake
boundaries are independent of resolution, by comparison maps and snake naturality, so
transport by the canonical right-derived comparisons defines the asserted boundaries.
The ordinary comparison is obtained from the inverse-image unit at the same site object.
Finite etale/pro-etale comparison is an isomorphism on derived sections over that object:
localize both sites at the etale object and apply global comparison. Thus the ordinary
comparison is an isomorphism in each degree. Its degree-zero component commutes with
restriction, transferring the degree-zero restriction isomorphism. Transfer the positive
ordinary vanishings using the comparison isomorphisms. On each site the localization long
exact sequence identifies H1 of the open with degree-two supported cohomology; it kills
support degrees zero and one using degree-zero restriction, and kills all degrees above
two using the ordinary vanishings. Define cZ by conjugating the ordinary degree-one
comparison by these two specified snake boundaries. This gives exactly the displayed
boundary square; no claim about an independently specified supported comparison is needed.
No choice of generator or residue is involved in this localization assertion. -/
theorem acyclic_pair_support_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (W : X.Etale) (j : W ⟶ Scheme.Etale.mk (𝟙 X)) [Mono j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hX : ∀ q : ℕ, 0 < q → IsZero (((sections X.smallEtaleTopology A
      (Scheme.Etale.mk (𝟙 X))).rightDerived q).obj F))
    (hU : ∀ q : ℕ, 2 ≤ q → IsZero (((sections X.smallEtaleTopology A W).rightDerived q).obj F))
    (hres : IsIso ((NatTrans.rightDerived
      (F := sections X.smallEtaleTopology A (Scheme.Etale.mk (𝟙 X)))
      (G := sections X.smallEtaleTopology A W)
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)).map j.op) 0).app F)) :
    let Fp := proCoefficient A X F
    let jp := (Scheme.toProEt X).map j
    let Z := Sheaf.supportedSectionsFunctor X.smallEtaleTopology (ModuleCat.{u + 1} A) j
    let Zp := Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A) jp
    ∃ (δ : ((sections X.smallEtaleTopology A W).rightDerived 1).obj F ⟶
          (Z.rightDerived 2).obj F)
      (δp : ((sections (Scheme.ProEt.topology X) A
        ((Scheme.toProEt X).obj W)).rightDerived 1).obj Fp ⟶ (Zp.rightDerived 2).obj Fp),
      IsBoundary X.smallEtaleTopology A j F δ ∧
      IsBoundary (Scheme.ProEt.topology X) A jp Fp δp ∧
      IsIso δ ∧ IsIso δp ∧ IsIso ((comparisonCohomology A X W 1).app F) ∧
      ∃ cZ : (Z.rightDerived 2).obj F ≅ (Zp.rightDerived 2).obj Fp,
        δ ≫ cZ.hom = (comparisonCohomology A X W 1).app F ≫ δp ∧
        ∀ q : ℕ, q ≠ 2 → IsZero ((Z.rightDerived q).obj F) ∧
          IsZero ((Zp.rightDerived q).obj Fp) := by
  let Fp := proCoefficient A X F
  let jp := (Scheme.toProEt X).map j
  have : Mono jp := by
    dsimp [jp]
    infer_instance
  have hcomp (T : X.Etale) (q : ℕ) :
      IsIso ((comparisonCohomology A X T q).app F) := by
    have := comparisonCohomology_isIso A X T q
    infer_instance
  have hXp (q : ℕ) (hq : 0 < q) :
      IsZero (((sections (Scheme.ProEt.topology X) A
        ((Scheme.toProEt X).obj (Scheme.Etale.mk (𝟙 X)))).rightDerived q).obj Fp) := by
    have := hcomp (Scheme.Etale.mk (𝟙 X)) q
    exact (hX q hq).of_iso (asIso
      ((comparisonCohomology A X (Scheme.Etale.mk (𝟙 X)) q).app F)).symm
  have hUp (q : ℕ) (hq : 2 ≤ q) :
      IsZero (((sections (Scheme.ProEt.topology X) A
        ((Scheme.toProEt X).obj W)).rightDerived q).obj Fp) := by
    have := hcomp W q
    exact (hU q hq).of_iso (asIso ((comparisonCohomology A X W q).app F)).symm
  have hr : IsIso (F.obj.map j.op) :=
    (restriction_zero_isIso_iff X.smallEtaleTopology A j F).mp hres
  have hrp : IsIso (Fp.obj.map jp.op) := by
    let η := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app F
    have hη (T : X.Etale) : IsIso (η.hom.app (op T)) := by
      have := comparisonSections_isIso A X T
      change IsIso ((comparisonSections A X T).app F)
      infer_instance
    have := hη W
    have := hη (Scheme.Etale.mk (𝟙 X))
    have hn : F.obj.map j.op ≫ η.hom.app (op W) =
        η.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫ Fp.obj.map jp.op := by
      exact η.hom.naturality j.op
    exact IsIso.of_isIso_fac_left hn.symm
  have hresp : IsIso ((NatTrans.rightDerived
      (F := sections (Scheme.ProEt.topology X) A
        ((Scheme.toProEt X).obj (Scheme.Etale.mk (𝟙 X))))
      (G := sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W))
      ((sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map jp.op) 0).app Fp) :=
    (restriction_zero_isIso_iff (Scheme.ProEt.topology X) A jp Fp).mpr hrp
  obtain ⟨δ, hδ, hi, hz⟩ := localization_consequences X.smallEtaleTopology A j F hX hU hres
  obtain ⟨δp, hδp, hip, hzp⟩ :=
    localization_consequences (Scheme.ProEt.topology X) A jp Fp hXp hUp hresp
  have := hi
  have := hip
  have hc := hcomp W 1
  let c := (asIso δ).symm ≪≫ asIso ((comparisonCohomology A X W 1).app F) ≪≫ asIso δp
  refine ⟨δ, δp, hδ, hδp, hi, hip, hc, c, ?_, ?_⟩
  · simp [c]
  · intro q hq
    exact ⟨hz q hq, hzp q hq⟩

end WeilConjectures.PurityFiniteSetting.RankOne
