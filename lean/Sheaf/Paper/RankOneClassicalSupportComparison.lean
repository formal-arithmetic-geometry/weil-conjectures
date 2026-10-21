/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneLocalData
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Classical support boundaries and site comparison

Source: Milne, Lectures on Etale Cohomology, Section 14, Proposition 14.3,
and Section 16, Example 16.3; blueprint sk-prop-a1-kummer, Coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

attribute [local implicit_reducible] Functor.mapHomologicalComplex
  HomologicalComplex.homologyFunctor


open AlgebraicGeometry.ProEtale

private noncomputable def evaluationComparisonIso
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) :
    ((sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W)).rightDerived q).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M) ≅
      ((sections X.smallEtaleTopology A W).rightDerived q).obj M := by
  have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} A) X
  have : (comparisonLowerStar (ModuleCat.{u + 1} A) X).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (comparisonAdjunction (ModuleCat.{u + 1} A) X)
  -- the global sections of a pro-étale sheaf are the global sections of its restriction
  let eΓ : comparisonLowerStar (ModuleCat.{u + 1} A) X ⋙ sections X.smallEtaleTopology A W ≅
      sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W) :=
    Iso.refl _
  let eR : (comparisonLowerStar (ModuleCat.{u + 1} A) X ⋙ sections X.smallEtaleTopology A
      W).rightDerived q ≅
      (sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W)).rightDerived q :=
    { hom := NatTrans.rightDerived eΓ.hom q
      inv := NatTrans.rightDerived eΓ.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, eΓ.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, eΓ.inv_hom_id, NatTrans.rightDerived_id] }
  -- the derived unit `M ⟶ Rν_* ν^* M` is invertible
  have hu := (comparisonAdjunction (ModuleCat.{u + 1} A)
      X).isIso_derivedPlus_unit_app_of_rightAcyclic
    (fun _ _ ↦ inferInstance) (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective
      (ModuleCat.{u + 1} A) X I)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj M)
  let e : (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (comparisonLowerStar (ModuleCat.{u + 1} A) X ⋙ sections X.smallEtaleTopology A
      W).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).obj ((comparisonUpperStar
      (ModuleCat.{u + 1} A) X).obj M) ≅
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (sections X.smallEtaleTopology A W).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).obj M :=
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).mapIso
      ((Functor.rightDerivedFunctorPlusCompIso _ _).app _ ≪≫
        (sections X.smallEtaleTopology A W).rightDerivedFunctorPlus.mapIso
          ((comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctorPlus.mapIso
            (((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusSingleFunctor
      0).app M).symm ≪≫
          (asIso ((comparisonAdjunction (ModuleCat.{u + 1} A) X).derivedPlus.unit.app _)).symm))
  exact eR.symm.app _ ≪≫
    ((comparisonLowerStar (ModuleCat.{u + 1} A) X ⋙ sections X.smallEtaleTopology A W)
      |>.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).symm.app _ ≪≫ e ≪≫
    ((sections X.smallEtaleTopology A
      W).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).app M


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem supportModule_restriction_epi
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Type (u + 1)) [CommRing R] [HasSheafify J (ModuleCat.{u + 1} R)]
    (I : Sheaf J (ModuleCat.{u + 1} R)) [Injective I]
    {W V : C} (j : W ⟶ V) [Mono j] : Epi (I.obj.map j.op) := by
  have : Injective I.obj := Injective.injective_of_adjoint (sheafificationAdjunction J _) I
  let a : (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free R) ⟶
      (uliftYoneda.{u + 1}.obj V ⋙ ModuleCat.free R) :=
    Functor.whiskerRight (uliftYoneda.{u + 1}.map j) (ModuleCat.free R)
  have : Mono a := by
    have (T : Cᵒᵖ) : Mono (a.app T) := by
      rw [ModuleCat.mono_iff_injective]
      apply Finsupp.mapDomain_injective
      intro x y h
      apply ULift.ext
      exact (cancel_mono j).1 (congrArg ULift.down h)
    exact NatTrans.mono_of_mono_app a
  rw [ModuleCat.epi_iff_surjective]
  intro s
  let b : (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free R) ⟶ I.obj :=
    { app := fun T ↦ ModuleCat.freeDesc (↾fun g ↦ I.obj.map g.down.op s)
      naturality := by
        intro T T' g
        apply ModuleCat.free_hom_ext
        intro x
        simp only [Functor.comp_map, ConcreteCategory.comp_apply]
        erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        change I.obj.map ((g.unop ≫ x.down).op) s = _
        rw [op_comp, I.obj.map_comp]
        rfl }
  obtain ⟨g, hg⟩ := Injective.factors b a
  refine ⟨g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V))), ?_⟩
  have he := congrArg (fun f ↦ f.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W)))) hg
  have hn := ConcreteCategory.congr_hom (g.naturality j.op)
    (ModuleCat.freeMk (ULift.up (𝟙 V)))
  have he' : g.app (op W) (ModuleCat.freeMk (ULift.up j)) = s := by
    simpa [a, b, ModuleCat.free_map_apply, ModuleCat.freeDesc_apply] using he
  have hn' : I.obj.map j.op (g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V)))) =
      g.app (op W) (ModuleCat.freeMk (ULift.up j)) := by
    simpa [ModuleCat.free_map_apply] using hn.symm
  exact hn'.trans he'


private theorem sectionComplex_shortExact
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    {V W : C} (j : W ⟶ V) [Mono j]
    {F : Sheaf J (ModuleCat.{u + 1} A)} (I : InjectiveResolution F) :
    (sectionComplex J A j I.cocomplex).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact ShortComplex.kernelSequence_exact _
  · change Mono (kernel.ι _)
    infer_instance
  · exact supportModule_restriction_epi J A (I.cocomplex.X n) j

private theorem boundary_exists
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {V W : C} (j : W ⟶ V) [Mono j] (F : Sheaf J (ModuleCat.{u + 1} A)) :
    ∃ δ : ((sections J A W).rightDerived 1).obj F ⟶
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived 2).obj F,
      IsBoundary J A j F δ := by
  let I₀ := injectiveResolution F
  let h₀ := sectionComplex_shortExact J A j I₀
  let δ₀ : ((sections J A W).rightDerived 1).obj F ⟶
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived 2).obj F :=
    (I₀.isoRightDerivedObj (sections J A W) 1).hom ≫ h₀.δ 1 2 support_degree_relation ≫
      (I₀.isoRightDerivedObj
        (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv
  refine ⟨δ₀, ?_⟩
  intro I
  let hI := sectionComplex_shortExact J A j I
  let a := InjectiveResolution.desc (𝟙 F) I I₀
  let E := sections J A W
  let Z := Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j
  let φ : sectionComplex J A j I₀.cocomplex ⟶ sectionComplex J A j I.cocomplex :=
    { τ₁ := (Z.mapHomologicalComplex (.up ℕ)).map a
      τ₂ := ((sections J A V).mapHomologicalComplex (.up ℕ)).map a
      τ₃ := (E.mapHomologicalComplex (.up ℕ)).map a
      comm₁₂ := by
        exact ((NatTrans.mapHomologicalComplex
          (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j) (.up ℕ)).naturality a)
      comm₂₃ := by
        exact ((NatTrans.mapHomologicalComplex
          ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) (.up ℕ)).naturality a) }
  have hE := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 F) I₀ I a (InjectiveResolution.desc_commutes_zero _ _ _) E 1
  have hZ := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (𝟙 F) I₀ I a (InjectiveResolution.desc_commutes_zero _ _ _) Z 2
  have hE' : (I.isoRightDerivedObj E 1).hom = (I₀.isoRightDerivedObj E 1).hom ≫
      HomologicalComplex.homologyMap ((E.mapHomologicalComplex (.up ℕ)).map a) 1 := by
    calc
      _ = 𝟙 _ ≫ (I.isoRightDerivedObj E 1).hom := (Category.id_comp _).symm
      _ = (E.rightDerived 1).map (𝟙 F) ≫ (I.isoRightDerivedObj E 1).hom :=
        congrArg (fun t ↦ t ≫ (I.isoRightDerivedObj E 1).hom)
          ((E.rightDerived 1).map_id F).symm
      _ = _ := hE
  have hZ' : (I₀.isoRightDerivedObj Z 2).inv =
      HomologicalComplex.homologyMap ((Z.mapHomologicalComplex (.up ℕ)).map a) 2 ≫
        (I.isoRightDerivedObj Z 2).inv := by
    calc
      _ = (I₀.isoRightDerivedObj Z 2).inv ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = (I₀.isoRightDerivedObj Z 2).inv ≫ (Z.rightDerived 2).map (𝟙 F) :=
        congrArg (fun t ↦ (I₀.isoRightDerivedObj Z 2).inv ≫ t)
          ((Z.rightDerived 2).map_id F).symm
      _ = _ := hZ
  have hδ := HomologicalComplex.HomologySequence.δ_naturality φ h₀ hI 1 2 support_degree_relation
  refine ⟨hI, ?_⟩
  dsimp only [δ₀]
  erw [hE']
  simp only [Category.assoc]
  erw [← reassoc_of% hδ, ← hZ']

/-- Ordinary comparison is invertible in every degree, and each site's support
boundary is normalized on every injective resolution.
Source: Stacks Tag 099W, Milne Section 9 Theorem 9.4.

Proof: evaluate comparison direct image at the same etale object. It preserves
injectives, and the derived comparison unit is invertible. Thus pulled-back etale
injectives are evaluation-acyclic; canonical derived base change is invertible.
For support, injectivity makes restriction along the monomorphism surjective.
The short exact sequence of section complexes has a snake boundary, independent
of the chosen resolution by a lift of the identity and snake naturality.
(blueprint: lem-pur-rank-one-classical-support-comparison). -/
theorem classical_support_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) {V W : X.Etale} (j : W ⟶ V) [Mono j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (∀ (T : X.Etale) (q : ℕ), IsIso ((comparisonCohomology A X T q).app F)) ∧
    (∃ δet, IsBoundary X.smallEtaleTopology A j F δet) ∧
    (∃ δpro, IsBoundary (Scheme.ProEt.topology X) A ((Scheme.toProEt X).map j)
      (proCoefficient A X F) δpro) := by
  refine ⟨?_, boundary_exists X.smallEtaleTopology A j F,
    boundary_exists (Scheme.ProEt.topology X) A ((Scheme.toProEt X).map j) _⟩
  intro T q
  let G := sections X.smallEtaleTopology A T
  let G' := sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj T)
  let β := comparisonUpperStar (ModuleCat.{u + 1} A) X
  have hu : IsIso (comparisonSections A X T) := by
    have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} A) X
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    change IsIso (((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app M).hom.app _)
    infer_instance
  have hacy (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) [Injective I] :
      G'.rightAcyclic (β.obj I) := by
    intro n
    exact (Functor.rightAcyclic_of_injective I n).of_iso
      (evaluationComparisonIso A X T I (n + 1))
  have := Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (G := G) (G' := G') (β := β) (γ := 𝟭 (ModuleCat.{u + 1} A))
    (asIso (comparisonSections A X T)) (fun I _ ↦ hacy I)
  change IsIso (Functor.rightDerivedFunctorPlusBaseChange (comparisonSections A X T)) at this
  change IsIso ((Functor.rightDerivedBaseChange (comparisonSections A X T) q).app F)
  have hd : IsIso (Functor.rightDerivedBaseChange (comparisonSections A X T) q) := by
    unfold Functor.rightDerivedBaseChange
    infer_instance
  infer_instance

end WeilConjectures.PurityFiniteSetting.RankOne
