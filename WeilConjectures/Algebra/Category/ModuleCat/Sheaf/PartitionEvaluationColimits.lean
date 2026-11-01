/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
import WeilConjectures.CategoryTheory.Sites.IsDisjointCover.DisjointSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator

/-! # Colimits of sections over finite partition objects

Source: Stacks Project, Tags 0935 and 0F63.
(blueprint: lem-zl-partition-evaluation-colimits).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r wJ uJ
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type c} [Category.{v} C]

variable (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- Every section of a coproduct over a finite-partition object factors through
a finite subcoproduct.
View the coproduct as the filtered colimit of finite subcoproducts. Local representatives
and a finite covering refinement give a common finite support. The projection onto that
support fixes the section locally, hence globally by separatedness.
Source: Stacks Project, Tag 0935 (2); the finite-support paragraph of the blueprint proof.
(blueprint: lem-zl-partition-evaluation-colimits). -/
private theorem partition_coproduct_section_finite_support
    (R : Sheaf J RingCat.{r})
    (W : C) (hW : J.HasFiniteDisjointRefinements W)
    (K : Type (max c v r)) (H : K → SheafOfModules.{max c v r} R)
    (s : (∐ H).val.obj (op W)) :
    ∃ (S : Finset K) (t : (∐ (fun k : S ↦ H k.val)).val.obj (op W)),
      (Sigma.desc (fun k : S ↦ Sigma.ι H k.val)).val.app (op W) t = s := by
  classical
  let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor H)
  let c := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone H
  let hc := CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone H
  let F := D ⋙ SheafOfModules.forget R
  let P := colimit F
  let k : P ⟶ (∐ H).val := colimit.desc F ((SheafOfModules.forget R).mapCocone c)
  let q := (PresheafOfModules.toPresheaf R.obj).map k
  have : Presheaf.IsLocallySurjective (J) q :=
    colimit_comparison_locally_surjective R D c hc
  obtain ⟨n, V, f, hfd, hf⟩ := hW
    (Presheaf.imageSieve q s) (Presheaf.imageSieve_mem J q s)
  let I := Fin n
  have hcover := hfd.ofArrows_mem
  have hrep (i : I) : ∃ (S : Finset (Discrete K))
      (t : (∐ (fun j : S ↦ H j.val.as)).val.obj (op (V i))),
      (Sigma.desc (fun j : S ↦ Sigma.ι H j.val.as)).val.app (op (V i)) t =
        (∐ H).val.map (f i).op s := by
    obtain ⟨t, ht⟩ := hf i
    let E := PresheafOfModules.evaluation.{max c v r} R.obj (op (V i)) ⋙
      forget₂ _ AddCommGrpCat.{max c v r} ⋙ CategoryTheory.forget _
    have : PreservesColimit F E := by dsimp [E]; infer_instance
    obtain ⟨j, a, ha⟩ := Types.jointly_surjective (F ⋙ E)
      (isColimitOfPreserves E (colimit.isColimit F)) t
    refine ⟨j, a, ?_⟩
    have hk := colimit.ι_desc ((SheafOfModules.forget R).mapCocone c) j
    have hk' := congrArg (fun g ↦ g.app (op (V i)) a) hk
    change k.app (op (V i)) ((colimit.ι F j).app (op (V i)) a) =
      (c.ι.app j).val.app (op (V i)) a at hk'
    change (colimit.ι F j).app (op (V i)) a = t at ha
    rw [ha] at hk'
    exact hk'.symm.trans ht
  let : Fintype I := Fintype.ofFinite I
  choose S t ht using hrep
  let S' : Finset K := (Finset.univ.biUnion S).image Discrete.as
  have hS (i : I) (j : S i) : j.val.as ∈ S' := by
    exact Finset.mem_image.mpr ⟨j.val,
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, j.property⟩, rfl⟩
  let inc : (∐ (fun j : S' ↦ H j.val)) ⟶ ∐ H :=
    Sigma.desc (fun j ↦ Sigma.ι H j.val)
  let p : (∐ H) ⟶ ∐ (fun j : S' ↦ H j.val) :=
    Sigma.desc (fun j ↦ if h : j ∈ S' then
      Sigma.ι (fun j : S' ↦ H j.val) ⟨j, h⟩ else 0)
  refine ⟨S', p.val.app (op W) s, ?_⟩
  let G : Sheaf (J) (Type (max c v r)) :=
    (sheafCompose (J)
      (CategoryTheory.forget AddCommGrpCat.{max c v r})).obj
      ((SheafOfModules.toSheaf R).obj (∐ H))
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSheafFor _ hcover).isSeparatedFor.ext
  intro Z g hg
  obtain ⟨i⟩ := hg
  change (∐ H).val.map (f i).op
    (inc.val.app (op W) (p.val.app (op W) s)) = (∐ H).val.map (f i).op s
  rw [← PresheafOfModules.naturality_apply inc.val,
    ← PresheafOfModules.naturality_apply p.val, ← ht i]
  let inci : (∐ (fun j : S i ↦ H j.val.as)) ⟶ ∐ H :=
    Sigma.desc (fun j ↦ Sigma.ι H j.val.as)
  have he : inci ≫ p ≫ inc = inci := by
    apply Sigma.hom_ext
    intro j
    simp [inci, p, inc, hS i j]
  exact congrArg (fun e ↦ e.val.app (op (V i)) (t i)) he

/-- The coproduct comparison is bijective: finite-support sections lift through a finite
comparison isomorphism. A kernel element likewise comes from a finite subcoproduct,
whose split inclusion and invertible comparison force the element to vanish.
Source: the direct-sum injectivity and surjectivity paragraphs of the blueprint proof.
(blueprint: lem-zl-partition-evaluation-colimits). -/
private theorem partition_evaluation_coproduct_isIso
    (R : Sheaf J RingCat.{r})
    (W : C) (hW : J.HasFiniteDisjointRefinements W)
    (K : Type (max c v r)) (H : K → SheafOfModules.{max c v r} R) :
    IsIso (sigmaComparison (SheafOfModules.evaluation.{max c v r} R (op W)) H) := by
  classical
  let ev := SheafOfModules.evaluation.{max c v r} R (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteCoproducts ev := by infer_instance
  let E := fun i ↦ ev.obj (H i)
  let q := sigmaComparison ev H
  have hfinite (S : Finset K) : IsIso (sigmaComparison ev (fun i : S ↦ H i.val)) := by
    infer_instance
  have hcomp (S : Finset K) :
      Sigma.desc (fun i : S ↦ Sigma.ι E i.val) ≫ q =
        sigmaComparison ev (fun i : S ↦ H i.val) ≫
          ev.map (Sigma.desc (fun i : S ↦ Sigma.ι H i.val)) := by
    apply Sigma.hom_ext
    intro i
    simp [q, E]
  apply (ConcreteCategory.isIso_iff_bijective q).mpr
  refine ⟨?_, ?_⟩
  · apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro z hz
    let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor E)
    have hc := isColimitOfPreserves
      (forget₂ (ModuleCat.{max c v r} _) AddCommGrpCat ⋙ CategoryTheory.forget _)
      (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone E)
    obtain ⟨S, t, ht⟩ := Types.jointly_surjective
      (D ⋙ CategoryTheory.forget _) hc z
    change (Sigma.desc (fun i : S ↦ Sigma.ι E i.val.as)) t = z at ht
    let H' := fun i : S ↦ H i.val.as
    let inc : (∐ H') ⟶ ∐ H := Sigma.desc (fun i ↦ Sigma.ι H i.val.as)
    let p : (∐ H) ⟶ ∐ H' := Sigma.desc (fun i ↦ if h : Discrete.mk i ∈ S then
      Sigma.ι H' ⟨⟨i⟩, h⟩ else 0)
    have hp : inc ≫ p = 𝟙 _ := by
      apply Sigma.hom_ext
      intro i
      simp [inc, p, H', i.property]
    have hq : sigmaComparison ev H' ≫ ev.map inc ≫ ev.map p =
        sigmaComparison ev H' := by rw [← ev.map_comp, hp, ev.map_id, Category.comp_id]
    have he : (ev.map inc) ((sigmaComparison ev H') t) = 0 := by
      have hh : Sigma.desc (fun i : S ↦ Sigma.ι E i.val.as) ≫ q =
          sigmaComparison ev H' ≫ ev.map inc := by
        apply Sigma.hom_ext
        intro i
        simp [inc, H', q, E]
      rw [← ModuleCat.comp_apply, ← hh, ModuleCat.comp_apply, ht]
      exact hz
    have hzero : (sigmaComparison ev H') t = 0 := by
      have hh := congrArg (ev.map p) he
      simpa only [← ModuleCat.comp_apply, Category.assoc, hq, map_zero] using hh
    have htzero : t = 0 := (ModuleCat.mono_iff_injective (sigmaComparison ev H')).mp
      (by infer_instance) (hzero.trans (map_zero _).symm)
    rw [← ht, htzero, map_zero]
  · intro s
    obtain ⟨S, t, ht⟩ := partition_coproduct_section_finite_support J R W hW K H s
    have : IsIso (sigmaComparison ev (fun i : S ↦ H i.val)) := hfinite S
    let a := inv (sigmaComparison ev (fun i : S ↦ H i.val)) t
    refine ⟨(Sigma.desc (fun i : S ↦ Sigma.ι E i.val)) a, ?_⟩
    rw [← ModuleCat.comp_apply, hcomp S, ModuleCat.comp_apply]
    dsimp only [a]
    rw [IsIso.inv_hom_id_apply]
    exact ht

/-- Evaluation on a finite-partition object preserves section-universe coproducts.
Source: Stacks Project, Tag 0935 (2), and the blueprint direct-sum argument above.
(blueprint: lem-zl-partition-evaluation-colimits). -/
private theorem partition_evaluation_preserves_coproducts
    (R : Sheaf J RingCat.{r})
    (W : C) (hW : J.HasFiniteDisjointRefinements W) (K : Type (max c v r)) :
    PreservesColimitsOfShape (Discrete K)
      (SheafOfModules.evaluation.{max c v r} R (op W)) := by
  let ev := SheafOfModules.evaluation.{max c v r} R (op W)
  have (H : K → SheafOfModules.{max c v r} R) : PreservesColimit (Discrete.functor H) ev := by
    have : IsIso (sigmaComparison ev H) := partition_evaluation_coproduct_isIso J R W hW K H
    exact PreservesCoproduct.of_iso_comparison ev H
  exact preservesColimitsOfShape_of_discrete ev

/-- Evaluation at an object with finite disjoint refinements preserves colimits
of every size for which the colimits exist.

Source: Stacks Project, Tags 0935 and 0F63
(blueprint: lem-zl-partition-evaluation-colimits).

Proof: a locally surjective morphism of sheaves is surjective on sections: choose
local lifts on a finite disjoint refinement and glue. Thus evaluation is exact.
Write a coproduct as the filtered colimit of its finite subcoproducts. Local
representatives of a section have finite supports; a finite partition refinement
bounds these supports by a single finite set. Separatedness then shows that the
section lies in that finite subcoproduct. Finite comparisons and split inclusions
prove that the full coproduct comparison is bijective. Coequalizers and coproducts
give preservation of colimits in the common universe. Shrink the hom types and
apply the special adjoint functor theorem to obtain a right adjoint to evaluation;
its left adjoint property gives preservation in the remaining diagram universes. -/
theorem evaluation_preservesColimits_of_finiteDisjointRefinements
    (R : Sheaf J RingCat.{r}) (W : C) (hW : J.HasFiniteDisjointRefinements W) :
    PreservesColimitsOfSize.{wJ, uJ} (evaluation.{max c v r} R (op W)) := by
  let ev := evaluation.{max c v r} R (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (toSheaf R).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max c v r} g).mpr inferInstance
    let g' := (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max c v r})).map g
    have : Sheaf.IsLocallySurjective g' := inferInstance
    apply (ModuleCat.epi_iff_surjective (ev.map f)).mpr
    intro y
    obtain ⟨n, Y, a, ha, hmem⟩ := hW _
      (Presheaf.imageSieve_mem J g'.hom y)
    choose t ht using hmem
    obtain ⟨x, hx⟩ := GrothendieckTopology.IsDisjointCover.exists_type_map_eq ha ((sheafCompose J
      (CategoryTheory.forget AddCommGrpCat.{max c v r})).obj ((toSheaf R).obj M)) t
    refine ⟨x, ?_⟩
    apply GrothendieckTopology.IsDisjointCover.type_ext ha ((sheafCompose J
      (CategoryTheory.forget AddCommGrpCat.{max c v r})).obj ((toSheaf R).obj N))
    intro i
    change ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max c v r})).obj
      ((toSheaf R).obj N)).obj.map (a i).op (g'.hom.app (op W) x) = _
    rw [← NatTrans.naturality_apply g'.hom]
    rw [hx i]
    exact ht i
  have : ev.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels ev
  have : PreservesFiniteColimits ev :=
    Functor.preservesFiniteColimits_of_preservesHomology ev
  have (K : Type (max c v r)) : PreservesColimitsOfShape (Discrete K) ev :=
    partition_evaluation_preserves_coproducts J R W hW K
  have : PreservesColimitsOfSize.{max c v r, max c v r} ev :=
    preservesColimits_of_preservesCoequalizers_and_coproducts ev
  have : IsGrothendieckAbelian.{max c v r} (SheafOfModules.{max c v r} R) :=
    isGrothendieckAbelianOfUniverses J R
  let e := ShrinkHoms.equivalence.{max c v r} (SheafOfModules.{max c v r} R)
  let ev' := e.inverse ⋙ ev
  have : PreservesColimitsOfSize.{max c v r, max c v r} ev' := by
    dsimp [ev']; infer_instance
  have : ev'.IsLeftAdjoint :=
    isLeftAdjoint_of_preservesColimits_of_isSeparating (isSeparator_separator _) ev'
  let i : e.functor ⋙ ev' ≅ ev :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm ev ≪≫ ev.leftUnitor
  have : PreservesColimitsOfSize.{wJ, uJ} (e.functor ⋙ ev') := by infer_instance
  exact preservesColimits_of_natIso i

end SheafOfModules
