/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.FinitePresieveFilteredColimit
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Filtered colimits of profinite condensed actions

Source: Stacks Project, Tags 0738 and 03CO, with the induced action on sections
(blueprint: lem-sfb-profinite-action-filtered-colimit-creation).

## Main statement

- `Profinite.CondensedAction.filteredColimitCreation` states that a filtered colimit of
  internal modules with a profinite action is computed sectionwise and that the forgetful
  functor creates it.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction

/-- Evaluate the recorded section-module equivalence at a profinite parameter.
Source: Stacks Project, Tag 0738, sectionwise colimits
(blueprint: lem-sfb-profinite-action-filtered-colimit-creation). -/
def filteredColimitSectionFunctor
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (S : Profinite.{u}) :
    Modules R ⥤ ModuleCat.{u + 1}
      ((InternalAbelianSheafModule.sectionRings
        (coherentTopology Profinite.{u}) R.X).obj (op S)) :=
  InternalAbelianSheafModule.sectionModuleFunctor (coherentTopology Profinite.{u}) R.X ⋙
    SheafOfModules.evaluation _ (op S)

private theorem profinite_colimit_isSheaf
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ i, Presheaf.IsSheaf (coherentTopology Profinite.{u}) (D.obj i)) :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) c.pt := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (C := Profinite.{u}) _ _
      (forget AddCommGrpCat.{u + 1}),
    isSheaf_iff_isSheaf_of_type, isSheaf_coherent]
  intro B α _ X π hπ
  let F := (Functor.whiskeringRight Profinite.{u}ᵒᵖ AddCommGrpCat.{u + 1}
    (Type (u + 1))).obj (forget AddCommGrpCat.{u + 1})
  apply finitePresieve_isSheafFor_filteredColimit (D ⋙ F) (F.mapCocone c)
    (isColimitOfPreserves F hc) (Presieve.ofArrows X π)
    (Precoverage.ofArrows_mem_finite X π)
  intro i
  exact (isSheaf_coherent _).mp
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget (C := Profinite.{u}) _ _
        (forget AddCommGrpCat.{u + 1})).mp (hD i))) B α X π hπ

private theorem underlying_colimit_sections
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Modules R) :
    ∃ c : Cocone D, Nonempty (IsColimit c) ∧
      ∀ S : Profinite.{u}, Nonempty (IsColimit
        ((filteredColimitSectionFunctor R S).mapCocone c)) := by
  let E := InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) R.X
  let F := InternalAbelianSheafModule.sectionModuleFunctor
    (coherentTopology Profinite.{u}) R.X
  have : F.IsEquivalence := inferInstanceAs E.functor.IsEquivalence
  have : HasColimit D := Adjunction.hasColimit_of_comp_equivalence D F
  let c := colimit.cocone D
  let hc := colimit.isColimit D
  refine ⟨c, ⟨hc⟩, fun S ↦ ⟨?_⟩⟩
  let R' := ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat RingCat)).obj
      (InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) R.X))
  let U := SheafOfModules.toSheaf.{u + 1} R'
  have : PreservesColimitsOfShape I U :=
    ((moduleSheaves_colimits_forgetful R').2.2.2.2.2 I).2.1
  let D' := (D ⋙ F) ⋙ U
  have : CreatesColimit D'
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) := by
    apply Sheaf.createsColimitOfIsSheaf
    intro e he
    exact profinite_colimit_isSheaf I _ e he (fun i ↦ (D'.obj i).property)
  have : PreservesColimit D'
      ((sheafSections (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}).obj
        (op S)) := by
    change PreservesColimit D'
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op S))
    infer_instance
  have hab := isColimitOfPreserves
    ((sheafSections (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}).obj (op S))
    (isColimitOfPreserves U (isColimitOfPreserves F hc))
  exact isColimitOfReflects (forget₂ (ModuleCat _) AddCommGrpCat) hab

private theorem section_representatives
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Modules R} (c : Cocone D) (S : Profinite.{u})
    (hc : IsColimit ((filteredColimitSectionFunctor R S).mapCocone c))
    (x : sectionModule R c.pt S) :
    ∃ (i : I) (m : sectionModule R (D.obj i) S),
      ((c.ι.app i).hom.hom.app (op S)).hom m = x := by
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (ModuleCat _)) hc) x

section LiftAction

variable {R : Profinite.CondensedRing.{u}} [IsCommMonObj R.X]
  {J : Type u} [TopologicalSpace J] [Group J] [IsTopologicalGroup J]
  {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
  (N : I ⥤ ActionModule R J)
  (c : Cocone (N ⋙ forgetAction (R := R) (P := J)))

private def sectionActionHom (M : ActionModule R J) (S : Profinite.{u}) (g : C(S, J)) :
    (filteredColimitSectionFunctor R S).obj M.module ⟶
      (filteredColimitSectionFunctor R S).obj M.module :=
  ModuleCat.ofHom (X := sectionModule R M.module S) (Y := sectionModule R M.module S)
    (M.act S g)

private def actionEndCocone (S : Profinite.{u}) (g : C(S, J)) :
    Cocone ((N ⋙ forgetAction (R := R) (P := J)) ⋙
      filteredColimitSectionFunctor R S) where
  pt := (filteredColimitSectionFunctor R S).obj c.pt
  ι :=
    { app := fun i ↦ sectionActionHom (N.obj i) S g ≫
        (filteredColimitSectionFunctor R S).map (c.ι.app i)
      naturality := by
        intro i j f
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id]
        have he : (filteredColimitSectionFunctor R S).map (N.map f).val ≫
            sectionActionHom (N.obj j) S g =
            sectionActionHom (N.obj i) S g ≫
              (filteredColimitSectionFunctor R S).map (N.map f).val := by
          ext m
          exact ((N.map f).property S g m).symm
        change (filteredColimitSectionFunctor R S).map (N.map f).val ≫
          (sectionActionHom (N.obj j) S g ≫
            (filteredColimitSectionFunctor R S).map (c.ι.app j)) = _
        rw [← Category.assoc, he, Category.assoc, ← Functor.map_comp]
        exact congrArg (fun k ↦ sectionActionHom (N.obj i) S g ≫
          (filteredColimitSectionFunctor R S).map k) (c.w f) }

private def actionEnd
    (hs : ∀ S : Profinite.{u}, IsColimit
      ((filteredColimitSectionFunctor R S).mapCocone c))
    (S : Profinite.{u}) (g : C(S, J)) :
    Module.End ((InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) R.X).obj (op S)) (sectionModule R c.pt S) :=
  ((hs S).desc (actionEndCocone N c S g)).hom

omit [IsFiltered I] in
private theorem actionEnd_ι
    (hs : ∀ S : Profinite.{u}, IsColimit
      ((filteredColimitSectionFunctor R S).mapCocone c))
    (S : Profinite.{u}) (g : C(S, J)) (i : I)
    (m : sectionModule R (N.obj i).module S) :
    actionEnd N c hs S g (((c.ι.app i).hom.hom.app (op S)).hom m) =
      ((c.ι.app i).hom.hom.app (op S)).hom ((N.obj i).act S g m) :=
  ConcreteCategory.congr_hom ((hs S).fac (actionEndCocone N c S g) i) m

private def actionMonoidHom
    (hs : ∀ S : Profinite.{u}, IsColimit
      ((filteredColimitSectionFunctor R S).mapCocone c)) (S : Profinite.{u}) :
    C(S, J) →* Module.End ((InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) R.X).obj (op S)) (sectionModule R c.pt S) where
  toFun := actionEnd N c hs S
  map_one' := by
    ext x
    obtain ⟨i, m, rfl⟩ := section_representatives R c S (hs S) x
    rw [actionEnd_ι, map_one]
    rfl
  map_mul' := by
    intro g h
    ext x
    obtain ⟨i, m, rfl⟩ := section_representatives R c S (hs S) x
    change actionEnd N c hs S (g * h) _ =
      actionEnd N c hs S g (actionEnd N c hs S h _)
    rw [actionEnd_ι, actionEnd_ι, actionEnd_ι, map_mul]
    rfl

private theorem actionEnd_naturality
    (hs : ∀ S : Profinite.{u}, IsColimit
      ((filteredColimitSectionFunctor R S).mapCocone c))
    (S T : Profinite.{u}) (f : T ⟶ S) (g : C(S, J)) (x : sectionModule R c.pt S) :
    (c.pt.X.obj.map f.op).hom (actionEnd N c hs S g x) =
      actionEnd N c hs T (g.comp f.hom.hom) ((c.pt.X.obj.map f.op).hom x) := by
  obtain ⟨i, m, rfl⟩ := section_representatives R c S (hs S) x
  have hn (m : sectionModule R (N.obj i).module S) :
      (c.pt.X.obj.map f.op).hom (((c.ι.app i).hom.hom.app (op S)).hom m) =
        ((c.ι.app i).hom.hom.app (op T)).hom
          (((N.obj i).module.X.obj.map f.op).hom m) :=
    (ConcreteCategory.congr_hom ((c.ι.app i).hom.hom.naturality f.op) m).symm
  rw [actionEnd_ι, hn, hn, actionEnd_ι, (N.obj i).naturality]

private def liftedAction
    (hs : ∀ S : Profinite.{u}, IsColimit
      ((filteredColimitSectionFunctor R S).mapCocone c)) : ActionModule R J where
  module := c.pt
  act := actionMonoidHom N c hs
  naturality := actionEnd_naturality N c hs

private def liftedCocone
    (hs : ∀ S : Profinite.{u}, IsColimit
      ((filteredColimitSectionFunctor R S).mapCocone c)) : Cocone N where
  pt := liftedAction N c hs
  ι :=
    { app := fun i ↦ ⟨c.ι.app i, fun S g m ↦ (actionEnd_ι N c hs S g i m).symm⟩
      naturality := fun _ _ f ↦ Subtype.ext (c.ι.naturality f) }

private theorem desc_equivariant
    (hs : ∀ S : Profinite.{u}, IsColimit
      ((filteredColimitSectionFunctor R S).mapCocone c))
    (d : Cocone N) (f : c.pt ⟶ d.pt.module)
    (hf : ∀ i, c.ι.app i ≫ f = (d.ι.app i).val) :
    Equivariant (liftedAction N c hs) d.pt f := by
  intro S g x
  obtain ⟨i, m, rfl⟩ := section_representatives R c S (hs S) x
  have hw (m : sectionModule R (N.obj i).module S) :
      (f.hom.hom.app (op S)).hom (((c.ι.app i).hom.hom.app (op S)).hom m) =
        ((d.ι.app i).val.hom.hom.app (op S)).hom m :=
    ConcreteCategory.congr_hom (congr_app (congrArg (fun k ↦ k.hom.hom) (hf i))
      (op S)) m
  change (f.hom.hom.app (op S)).hom (actionEnd N c hs S g _) = _
  rw [actionEnd_ι, hw]
  exact ((d.ι.app i).property S g m).trans
    (congrArg (d.pt.act S g) (hw m).symm)

private def liftedIsColimit
    (hc : IsColimit c)
    (hs : ∀ S : Profinite.{u}, IsColimit
      ((filteredColimitSectionFunctor R S).mapCocone c)) :
    IsColimit (liftedCocone N c hs) where
  desc d := ⟨hc.desc ((forgetAction (R := R) (P := J)).mapCocone d),
    desc_equivariant N c hs d _ (hc.fac _)⟩
  fac d i := Subtype.ext (hc.fac _ i)
  uniq d f hf := by
    apply Subtype.ext
    exact hc.uniq ((forgetAction (R := R) (P := J)).mapCocone d) f.val
      (fun i ↦ congrArg Subtype.val (hf i))

end LiftAction

private theorem forgetAction_reflects
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    (J : Type u) [TopologicalSpace J] [Group J] [IsTopologicalGroup J] :
    (forgetAction (R := R) (P := J)).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have : IsIso f.val := hf
    let i := inv f.val
    have hi : Equivariant N M i := by
      intro S g x
      have hf (y : sectionModule R N.module S) :
          (f.val.hom.hom.app (op S)).hom ((i.hom.hom.app (op S)).hom y) = y := by
        exact ConcreteCategory.congr_hom (congr_app
          (congrArg (fun k ↦ k.hom.hom) (IsIso.inv_hom_id f.val)) (op S)) y
      have hg (y : sectionModule R M.module S) :
          (i.hom.hom.app (op S)).hom ((f.val.hom.hom.app (op S)).hom y) = y := by
        exact ConcreteCategory.congr_hom (congr_app
          (congrArg (fun k ↦ k.hom.hom) (IsIso.hom_inv_id f.val)) (op S)) y
      have h := congrArg (fun y ↦ (i.hom.hom.app (op S)).hom y)
        (f.property S g ((i.hom.hom.app (op S)).hom x))
      rw [hg, hf] at h
      exact h.symm
    exact ⟨⟨⟨i, hi⟩, Subtype.ext (IsIso.hom_inv_id f.val),
      Subtype.ext (IsIso.inv_hom_id f.val)⟩⟩

/-- A filtered colimit of internal modules with a compact totally disconnected profinite-group
action is created by forgetting the action.  Its sections are represented by stage sections,
with equality detected at a common stage, and the action is induced by `g [m] = [g m]`.

Source: Stacks Project, Tag 0738 (sites.tex, lemma-directed-colimits-sections), and Tag 03CO
(sites-modules.tex, lemma-limits-colimits-abelian-sheaves); the induced action and equivariant
universal property are the construction in the direct-images proof, paragraph (3)
(blueprint: lem-sfb-profinite-action-filtered-colimit-creation).

Proof: First use the finite-cover description of the coherent profinite topology and the
filtered-colimit theorem for sections to identify the underlying module colimit sectionwise.
The additive-group and set filtered-colimit descriptions give representatives and common-stage
criteria.  For `g : C(S,J)`, define `g [m] := [g m]`; equivariance of transition maps makes
this independent of representatives, and the group, linearity and restriction laws follow on
representatives.  The coprojections are equivariant.  Finally, the underlying colimit
factorization of any equivariant cocone is equivariant on each representative, so the same
factorization is the colimit in the action category and the forgetful functor creates it.
-/
theorem filteredColimitCreation
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    (J : Type u) [TopologicalSpace J] [Group J] [IsTopologicalGroup J]
    [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (N : I ⥤ ActionModule R J) :
    ∃ c : Cocone N,
      Nonempty (IsColimit ((forgetAction (R := R) (P := J)).mapCocone c)) ∧
      Nonempty (IsColimit c) ∧
      (∀ S : Profinite.{u}, Nonempty (IsColimit
        ((filteredColimitSectionFunctor R S).mapCocone
          ((forgetAction (R := R) (P := J)).mapCocone c)))) ∧
      (∀ (S : Profinite.{u})
        (x : sectionModule R c.pt.module S),
        ∃ (i : I) (m : sectionModule R (N.obj i).module S),
          ((c.ι.app i).val.hom.hom.app (op S)).hom m = x) ∧
      (∀ (S : Profinite.{u})
        (i j : I) (m : sectionModule R (N.obj i).module S)
          (n : sectionModule R (N.obj j).module S),
        ((c.ι.app i).val.hom.hom.app (op S)).hom m =
            ((c.ι.app j).val.hom.hom.app (op S)).hom n ↔
          ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k),
            ((N.map f).val.hom.hom.app (op S)).hom m =
              ((N.map g).val.hom.hom.app (op S)).hom n) ∧
      (∀ (S : Profinite.{u}) (g : C(S, J)) (i : I)
        (m : sectionModule R (N.obj i).module S),
        c.pt.act S g (((c.ι.app i).val.hom.hom.app (op S)).hom m) =
          ((c.ι.app i).val.hom.hom.app (op S)).hom ((N.obj i).act S g m)) ∧
      (∀ (d : Cocone N) (f : c.pt.module ⟶ d.pt.module),
        (∀ i : I, (c.ι.app i).val ≫ f = (d.ι.app i).val) →
          Equivariant c.pt d.pt f) ∧
      Nonempty (CreatesColimit N (forgetAction (R := R) (P := J))) := by
  classical
  obtain ⟨c, ⟨hc⟩, hs⟩ := underlying_colimit_sections R I
    (N ⋙ forgetAction (R := R) (P := J))
  let hs' := fun S ↦ (hs S).some
  let d := liftedCocone N c hs'
  have hu : (forgetAction (R := R) (P := J)).mapCocone d = c := rfl
  have hd := liftedIsColimit N c hc hs'
  have : (forgetAction (R := R) (P := J)).ReflectsIsomorphisms :=
    forgetAction_reflects R J
  refine ⟨d, ?_, ⟨hd⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu]
    exact ⟨hc⟩
  · intro S
    rw [hu]
    exact hs S
  · intro S x
    exact section_representatives R c S (hs' S) x
  · intro S i j m n
    exact Types.FilteredColimit.isColimit_eq_iff _
      (isColimitOfPreserves (forget (ModuleCat _)) (hs' S))
  · intro S g i m
    exact actionEnd_ι N c hs' S g i m
  · intro e f hf
    exact desc_equivariant N c hs' e f hf
  · exact ⟨createsColimitOfReflectsIso' hc
      ⟨⟨d, eqToIso hu⟩, hd⟩⟩

end Profinite.CondensedAction
