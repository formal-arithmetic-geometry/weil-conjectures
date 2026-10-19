/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Sheaf.CategoryTheory.PerfectConstantLocalChainRepresentative
import Sheaf.CategoryTheory.BoundedConstantChainMapLocal
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Derived maps out of a perfect constant complex are locally algebraic

Source: Stacks Project, Cohomology on Sites, Tag 09BE, `lemma-locally-constant-map`
(blueprint: lem-sfb-perfect-constant-derived-map-local).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wR wS wU

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : Sheaf J RingCat.{max u v}) {U V : C} (f : V ⟶ U)

private theorem overMap_exact
    [HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify (J.over V) AddCommGrpCat.{max u v}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    PreservesFiniteLimits (SheafOfModules.overMap.{max u v} S f) ∧
      PreservesFiniteColimits (SheafOfModules.overMap.{max u v} S f) := by
  let F := SheafOfModules.overMap.{max u v} S f
  let G := SheafOfModules.toSheaf.{max u v} (S.over V)
  let H := J.overMapPullback AddCommGrpCat.{max u v} f
  have : F.Additive := ⟨fun {_ _} a b ↦ by ext W x; rfl⟩
  let e : F ⋙ G ≅ SheafOfModules.toSheaf.{max u v} (S.over U) ⋙ H := Iso.refl _
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesFiniteLimits (F ⋙ G) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F G
  have : H.PreservesEpimorphisms := by
    constructor
    intro M N a ha
    have : Sheaf.IsLocallySurjective (A := AddCommGrpCat.{max u v}) a :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v} a).2 ha
    have : Sheaf.IsLocallySurjective (A := AddCommGrpCat.{max u v}) (H.map a) :=
      Presheaf.isLocallySurjective_whisker (J.over V) (J.over U) (Over.map f) a.hom
    exact Sheaf.epi_of_isLocallySurjective (A := AddCommGrpCat.{max u v}) (H.map a)
  have : F.PreservesEpimorphisms := by
    constructor
    intro M N a ha
    apply G.epi_of_epi_map
    have : PreservesFiniteColimits (SheafOfModules.toSheaf.{max u v} (S.over U)) :=
      inferInstance
    have : Epi ((SheafOfModules.toSheaf.{max u v} (S.over U)).map a) := inferInstance
    exact inferInstanceAs
      (Epi (H.map ((SheafOfModules.toSheaf.{max u v} (S.over U)).map a)))
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  exact ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology F⟩

private noncomputable def restrictionIso
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{max u v}]
    [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasDerivedCategory.{wS} (SheafOfModules.{max u v} S)]
    [∀ W : C, HasDerivedCategory.{wU} (SheafOfModules.{max u v} (S.over W))] :
    ringedDerivedRestrictionSized.{u, v, wS, wU} S U ⋙
        (by
          have : (SheafOfModules.overMap.{max u v} S f).Additive :=
            ⟨fun {_ _} a b ↦ by ext W x; rfl⟩
          have := (overMap_exact S f).1
          have := (overMap_exact S f).2
          exact (SheafOfModules.overMap.{max u v} S f).mapDerivedCategory) ≅
      ringedDerivedRestrictionSized.{u, v, wS, wU} S V := by
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S U).1
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S U).2.1
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S U).2.2
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S V).1
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S V).2.1
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S V).2.2
  have : (SheafOfModules.overMap.{max u v} S f).Additive :=
    ⟨fun {_ _} a b ↦ by ext W x; rfl⟩
  have := (overMap_exact S f).1
  have := (overMap_exact S f).2
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{max u v} S f)

private noncomputable def furtherCochainRestriction :
    CochainComplex (SheafOfModules.{max u v} (S.over U)) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v} (S.over V)) ℤ :=
  have : (SheafOfModules.overMap.{max u v} S f).Additive :=
    ⟨fun {_ _} a b ↦ by ext W x; rfl⟩
  (SheafOfModules.overMap.{max u v} S f).mapHomologicalComplex (.up ℤ)

private theorem restriction_map_eq
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{max u v}]
    [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasDerivedCategory.{wS} (SheafOfModules.{max u v} S)]
    [∀ W : C, HasDerivedCategory.{wU} (SheafOfModules.{max u v} (S.over W))]
    {K L : CochainComplex (SheafOfModules.{max u v} S) ℤ}
    (a : (moduleCochainRestriction S U).obj K ⟶ (moduleCochainRestriction S U).obj L)
    (b : K ⟶ L)
    (h : (furtherCochainRestriction S f).map a =
      (furtherCochainRestriction S f).map ((moduleCochainRestriction S U).map b))
    (ψ : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L)
    (ha : DerivedCategory.Q.map a =
      (moduleCochainRestrictionQIso.{u, v, wS, wU} S U K).inv ≫
        (ringedDerivedRestrictionSized.{u, v, wS, wU} S U).map ψ ≫
          (moduleCochainRestrictionQIso.{u, v, wS, wU} S U L).hom) :
    (ringedDerivedRestrictionSized.{u, v, wS, wU} S V).map ψ =
      (ringedDerivedRestrictionSized.{u, v, wS, wU} S V).map (DerivedCategory.Q.map b) := by
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S U).1
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S U).2.1
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S U).2.2
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S V).1
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S V).2.1
  have := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v} S V).2.2
  have : (SheafOfModules.overMap.{max u v} S f).Additive :=
    ⟨fun {_ _} a b ↦ by ext W x; rfl⟩
  have := (overMap_exact S f).1
  have := (overMap_exact S f).2
  let T : DerivedCategory.{wU} (SheafOfModules.{max u v} (S.over U)) ⥤
      DerivedCategory.{wU} (SheafOfModules.{max u v} (S.over V)) :=
    (SheafOfModules.overMap.{max u v} S f).mapDerivedCategory
  let e := restrictionIso S f
  change ((SheafOfModules.overMap.{max u v} S f).mapHomologicalComplex (.up ℤ)).map a =
    ((SheafOfModules.overMap.{max u v} S f).mapHomologicalComplex (.up ℤ)).map
      ((moduleCochainRestriction S U).map b) at h
  have hh : T.map (DerivedCategory.Q.map a) =
      T.map (DerivedCategory.Q.map ((moduleCochainRestriction S U).map b)) := by
    apply (cancel_mono ((SheafOfModules.overMap.{max u v} S f).mapDerivedCategoryFactors.hom.app
      ((moduleCochainRestriction S U).obj L))).mp
    rw [Functor.mapDerivedCategoryFactors_hom_naturality,
      Functor.mapDerivedCategoryFactors_hom_naturality, h]
  have hb : (ringedDerivedRestrictionSized.{u, v, wS, wU} S U).map (DerivedCategory.Q.map b) =
      (moduleCochainRestrictionQIso.{u, v, wS, wU} S U K).hom ≫
        DerivedCategory.Q.map ((moduleCochainRestriction S U).map b) ≫
          (moduleCochainRestrictionQIso.{u, v, wS, wU} S U L).inv := by
    apply (cancel_mono (moduleCochainRestrictionQIso.{u, v, wS, wU} S U L).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (SheafOfModules.overFunctor.{max u v} S U).mapDerivedCategoryFactors.hom.naturality b
  have hh' : T.map ((ringedDerivedRestrictionSized.{u, v, wS, wU} S U).map ψ) =
      T.map ((ringedDerivedRestrictionSized.{u, v, wS, wU} S U).map (DerivedCategory.Q.map b)) := by
    have hrep : (ringedDerivedRestrictionSized.{u, v, wS, wU} S U).map ψ =
        (moduleCochainRestrictionQIso.{u, v, wS, wU} S U K).hom ≫ DerivedCategory.Q.map a ≫
          (moduleCochainRestrictionQIso.{u, v, wS, wU} S U L).inv := by
      rw [ha]
      simp
    rw [hrep, hb, T.map_comp, T.map_comp, T.map_comp, T.map_comp, hh]
  apply (cancel_epi (e.hom.app (DerivedCategory.Q.obj K))).mp
  rw [← e.hom.naturality, ← e.hom.naturality]
  exact congrArg (fun t ↦ t ≫ e.hom.app (DerivedCategory.Q.obj L)) hh'


private theorem cover_bind_property
    {C : Type u} [Category.{v} C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    {X : C} {I : Type (max u v)} (U : I → C) (f : ∀ i, U i ⟶ X)
    (hf : Presieve.ofArrows U f ∈ J X) (P : C → Prop)
    (h : ∀ i, ∃ (S : Presieve (U i)), S ∈ J (U i) ∧
      ∀ (V : C) (g : V ⟶ U i), S g → P V) :
    ∃ (K : Type (max u v)) (V : K → C) (g : ∀ k, V k ⟶ X),
      Presieve.ofArrows V g ∈ J X ∧ ∀ k, P (V k) := by
  classical
  have h' : ∀ (Y : C) (a : Y ⟶ X) (_ : Presieve.ofArrows U f a),
      ∃ (S : Presieve Y), S ∈ J Y ∧ ∀ (V : C) (g : V ⟶ Y), S g → P V := by
    intro Y a ha
    cases ha with
    | mk i => exact h i
  choose S hS hP using h'
  let T := (Presieve.ofArrows U f).bind (fun {Y a} ha ↦ S Y a ha)
  have hT : T ∈ J X := hJ.2.1 X _ (fun {Y} a ha ↦ S Y a ha) hf hS
  let K := Σ Y : C, {a : Y ⟶ X // T a}
  let V : K → C := fun k ↦ k.1
  let g : ∀ k : K, V k ⟶ X := fun k ↦ k.2.1
  have he : Presieve.ofArrows V g = T := by
    funext Y a
    apply propext
    constructor
    · rintro ⟨k⟩
      exact k.2.2
    · intro ha
      exact Presieve.ofArrows.mk (Y := V) (f := g) ⟨Y, a, ha⟩
  refine ⟨K, V, g, he ▸ hT, ?_⟩
  intro k
  obtain ⟨Y, b, a, ha, hb, _⟩ := k.2.2
  exact hP Y a ha _ b hb

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A derived morphism between constant complexes, with perfect source and arbitrary
target, is induced locally by a morphism in the coefficient ring's derived category.
Source: Stacks Project, Cohomology on Sites, Tag 09BE, `lemma-locally-constant-map`
(blueprint: lem-sfb-perfect-constant-derived-map-local).

Proof:
1. Choose a bounded finite-projective model F of P and a complex model G of L.
   Perfectness supplies the first model and essential surjectivity of localization
   supplies the second. Use the canonical exact-functor localization comparisons to
   transport the given morphism to the constant complex models.
2. Apply the perfect-source local chain-representative theorem (Tag 09BD) to obtain
   actual chain representatives from the constant F to the constant G on a covering.
   No boundedness of G is needed.
3. Apply the bounded constant-chain algebraicity theorem to each representative.
   Its finite-generator argument lifts component images through the ambient constant
   units on a common refinement and reflects the chain equations through injective
   units. Empty-covered objects use the zero chain map.
4. Further slice restriction is exact: its underlying additive sheaf functor preserves
   finite limits and local surjectivity, hence preserves epimorphisms and cokernels.
   The derived composition comparison identifies iterated and direct restriction.
   Localization naturality transports the componentwise chain equality to the derived
   equality. Conjugate each localized algebraic chain map by the model isomorphisms;
   exact-functor factorization naturality and cancellation identify its constant
   realization with the given morphism on the refined slice. Compose the coverings
   using bind and reindex the resulting presieve by its arrows. No points are used. -/
theorem exists_perfect_constant_derived_map_local
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (X : C) (_hX : IsTerminal X)
    (R : Type (max u v)) [CommRing R]
    [HasDerivedCategory.{wR, max u v, (max u v) + 1} (ModuleCat.{max u v} R)]
    [siteModuleHasDerivedCategory.{u, v, wS}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))]
    [∀ U : C, siteModuleHasDerivedCategory.{max u v, v, wU}
      (((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)).over U)]
    (P L : DerivedCategory.{wR, max u v, (max u v) + 1} (ModuleCat.{max u v} R))
    (_hP : DerivedCategory.IsPerfectRingComplex.{max u v, wR} P)
    (φ : (siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj P ⟶
      (siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj L) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, ∃ α : P ⟶ L,
        (ringedDerivedRestrictionSized.{u, v, wS, wU}
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
          (U i)).map φ =
        (ringedDerivedRestrictionSized.{u, v, wS, wU}
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
          (U i)).map
          ((siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).map α) := by
  classical
  obtain ⟨F, a, b, hge, hle, hterms, ⟨eP⟩⟩ := _hP
  have : F.IsStrictlyGE a := hge
  have : F.IsStrictlyLE b := hle
  have hfin : ∀ q : ℤ, Module.Finite R (F.X q) := fun q ↦ (hterms q).2
  have hproj : ∀ q : ℤ, Module.Projective R (F.X q) := fun q ↦ (hterms q).1
  have hF : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q) := by
    refine ⟨min a b, max a b, min_le_max, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact F.isZero_of_isStrictlyGE a q (lt_of_lt_of_le hq (min_le_left _ _))
    · exact F.isZero_of_isStrictlyLE b q (lt_of_le_of_lt (le_max_right _ _) hq)
  let G := DerivedCategory.Q.objPreimage L
  let eL : DerivedCategory.Q.obj G ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let S := (constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)
  let D := siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R
  let T := constantModuleCochainFunctor.{u, v} J.toGrothendieck R
  have := (siteConstantModuleFunctorGeneral_exact.{u, v} J.toGrothendieck R).1
  have := (siteConstantModuleFunctorGeneral_exact.{u, v} J.toGrothendieck R).2.1
  have := (siteConstantModuleFunctorGeneral_exact.{u, v} J.toGrothendieck R).2.2
  let E : ModuleCat.{max u v} R ⥤ SheafOfModules.{max u v} S :=
    siteConstantModuleFunctorGeneral.{u, v} J.toGrothendieck R
  have : E.Additive := (siteConstantModuleFunctorGeneral_exact.{u, v} J.toGrothendieck R).1
  have : PreservesFiniteLimits E :=
    (siteConstantModuleFunctorGeneral_exact.{u, v} J.toGrothendieck R).2.1
  have : PreservesFiniteColimits E :=
    (siteConstantModuleFunctorGeneral_exact.{u, v} J.toGrothendieck R).2.2
  let eF : D.obj (DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.{wS, max u v, (max u v) + 1}.obj (T.obj F) :=
    (Functor.mapDerivedCategoryFactors.{wR, wS, max u v, max u v,
    (max u v) + 1, (max u v) + 1} E).app F
  let eG : D.obj (DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.{wS, max u v, (max u v) + 1}.obj (T.obj G) :=
    (Functor.mapDerivedCategoryFactors.{wR, wS, max u v, max u v,
    (max u v) + 1, (max u v) + 1} E).app G
  let cF := D.mapIso eP ≪≫ eF
  let cG := D.mapIso eL.symm ≪≫ eG
  let ψ := cF.inv ≫ φ ≫ cG.hom
  obtain ⟨I, U, f, hf, hrep⟩ := exists_perfect_constant_local_chain_representative
    J _hJ X _hX R F hF (T.obj G) ψ
  apply cover_bind_property J _hJ U f hf
    (fun V ↦ ∃ α : P ⟶ L,
      (ringedDerivedRestrictionSized.{u, v, wS, wU} S V).map φ =
      (ringedDerivedRestrictionSized.{u, v, wS, wU} S V).map (D.map α))
  intro i
  obtain ⟨a, ha⟩ := hrep i
  obtain ⟨W, hW, hlocal⟩ := exists_bounded_constant_chain_map_local J _hJ R F G hF (U i) a
  refine ⟨W, hW, fun V g hg ↦ ?_⟩
  obtain ⟨b, hb⟩ := hlocal V g hg
  have hb' : (furtherCochainRestriction S g).map a =
      (furtherCochainRestriction S g).map ((moduleCochainRestriction S (U i)).map
        (T.map b)) := by
    apply HomologicalComplex.hom_ext
    intro q
    exact hb q
  have hψ := restriction_map_eq.{u, v, wS, wU} S g a (T.map b) hb' ψ ha
  let α : P ⟶ L := eP.hom ≫ DerivedCategory.Q.map b ≫ eL.hom
  have hα : cF.inv ≫ D.map α ≫ cG.hom = DerivedCategory.Q.map (T.map b) := by
    dsimp [α, cF, cG, eF, eG, D, E, T, siteDerivedConstantModuleFunctor,
      constantModuleCochainFunctor]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
    rw [Functor.mapDerivedCategoryFactors_hom_naturality
      (siteConstantModuleFunctorGeneral.{u, v} J.toGrothendieck R) b]
    simp
  refine ⟨α, ?_⟩
  let H := ringedDerivedRestrictionSized.{u, v, wS, wU} S V
  have : IsIso (H.map cF.inv) := inferInstance
  have : IsIso (H.map cG.hom) := inferInstance
  apply (cancel_epi (H.map cF.inv)).mp
  apply (cancel_mono (H.map cG.hom)).mp
  rw [← hα] at hψ
  simpa only [ψ, Functor.map_comp, Category.assoc] using hψ

end CategoryTheory
