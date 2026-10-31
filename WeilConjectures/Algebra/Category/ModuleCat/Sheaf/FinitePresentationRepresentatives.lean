/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietorisSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Topology.GlueSheavesOfModulesSupplement
import WeilConjectures.Topology.ModuleLocalModelGluingDataSet
import Mathlib.Data.Fintype.EquivFin

/-!
# A set of representatives of finite-presentation module sheaves

Source: Stacks Project, Modules, Lemma 01BC and Definition 01BN
(blueprint: lem-weil-pbc-module-finite-presentation-representatives).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

private abbrev localIndex (X : RingedSpace.{u}) (U : Opens X) : Type u :=
  Σ m n : ℕ, SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin m)) ⟶
    SheafOfModules.free (ULift.{u} (Fin n))

private noncomputable def localModel (X : RingedSpace.{u}) (U : Opens X)
    (t : localIndex X U) : SheafOfModules.{u} ((moduleRings X).over U) :=
  cokernel t.2.2

set_option backward.isDefEq.respectTransparency false in
private theorem presentation_localModel (X : RingedSpace.{u}) (U : Opens X)
    (M : SheafOfModules.{u} ((moduleRings X).over U))
    (p : M.Presentation) [p.IsFinite] :
    ∃ t : localIndex X U, Nonempty (localModel X U t ≅ M) := by
  classical
  let _ := Fintype.ofFinite p.relations.I
  let _ := Fintype.ofFinite p.generators.I
  let er : p.relations.I ≃ ULift.{u} (Fin (Fintype.card p.relations.I)) :=
    (Fintype.equivFin _).trans Equiv.ulift.symm
  let eg : p.generators.I ≃ ULift.{u} (Fin (Fintype.card p.generators.I)) :=
    (Fintype.equivFin _).trans Equiv.ulift.symm
  let ar := (SheafOfModules.freeFunctor (R := (moduleRings X).over U)).mapIso er.toIso
  let ag := (SheafOfModules.freeFunctor (R := (moduleRings X).over U)).mapIso eg.toIso
  let f := p.relations.π ≫ kernel.ι p.generators.π
  let f' := ar.inv ≫ f ≫ ag.hom
  let g' := ag.inv ≫ p.generators.π
  have h : f' ≫ g' = 0 := by simp [f', g', f]
  have hc : IsColimit (CokernelCofork.ofπ g' h) :=
    IsCokernel.ofIso f p.isColimit (CokernelCofork.ofπ g' h) ar ag (Iso.refl M)
      (by simp [f']) (by simp [g'])
  refine ⟨⟨_, _, f'⟩, ⟨?_⟩⟩
  exact (cokernelIsCokernel f').coconePointUniqueUpToIso hc

@[irreducible]
private noncomputable def modelTransition (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) (U V : Opens X)
    {A : SheafOfModules.{u} ((moduleRings X).over U)}
    {B : SheafOfModules.{u} ((moduleRings X).over V)}
    (a : A ≅ F.over U) (b : B ≅ F.over V) :
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_left : U ⊓ V ⟶ U)).obj A ≅
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_right : U ⊓ V ⟶ V)).obj B :=
  (SheafOfModules.overMap (moduleRings X) (homOfLE inf_le_left)).mapIso a ≪≫
    (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE inf_le_left)).app F ≪≫
    ((SheafOfModules.overFunctorMap (moduleRings X) (homOfLE inf_le_right)).app F).symm ≪≫
    ((SheafOfModules.overMap (moduleRings X) (homOfLE inf_le_right)).mapIso b).symm

set_option backward.isDefEq.respectTransparency false in
private theorem modelTransition_app (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) (U V : Opens X)
    {A : SheafOfModules.{u} ((moduleRings X).over U)}
    {B : SheafOfModules.{u} ((moduleRings X).over V)}
    (a : A ≅ F.over U) (b : B ≅ F.over V)
    (W : Opens X) (hU : W ≤ U) (hV : W ≤ V) :
    (modelTransition X F U V a b).hom.val.app
        (op (Over.mk (homOfLE (le_inf hU hV)))) =
      a.hom.val.app (op (Over.mk (homOfLE hU))) ≫
        b.inv.val.app (op (Over.mk (homOfLE hV))) := by
  unfold modelTransition
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem iso_of_localComparisons (X : RingedSpace.{u}) (I : Type u)
    (U : I → Opens X) (hc : ⨆ i, U i = ⊤)
    (H F : SheafOfModules.{u} (moduleRings X))
    (χ : ∀ i, H.over (U i) ≅ F.over (U i))
    (hχ : ∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      (χ i).hom.val.app (op (Over.mk (homOfLE hi))) =
        (χ j).hom.val.app (op (Over.mk (homOfLE hj)))) : Nonempty (H ≅ F) := by
  have hχinv (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
      (χ i).inv.val.app (op (Over.mk (homOfLE hi))) =
        (χ j).inv.val.app (op (Over.mk (homOfLE hj))) := by
    let a : H.val.obj (op W) ⟶ F.val.obj (op W) :=
      (χ i).hom.val.app (op (Over.mk (homOfLE hi)))
    let a' : H.val.obj (op W) ⟶ F.val.obj (op W) :=
      (χ j).hom.val.app (op (Over.mk (homOfLE hj)))
    let b : F.val.obj (op W) ⟶ H.val.obj (op W) :=
      (χ i).inv.val.app (op (Over.mk (homOfLE hi)))
    let c : F.val.obj (op W) ⟶ H.val.obj (op W) :=
      (χ j).inv.val.app (op (Over.mk (homOfLE hj)))
    have hba : b ≫ a = 𝟙 _ := by
      change ((χ i).inv ≫ (χ i).hom).val.app _ = _
      rw [Iso.inv_hom_id]
      rfl
    have hac : a' ≫ c = 𝟙 _ := by
      change ((χ j).hom ≫ (χ j).inv).val.app _ = _
      rw [Iso.hom_inv_id]
      rfl
    have haa : a = a' := hχ i j W hi hj
    rw [← haa] at hac
    change b = c
    calc
      b = b ≫ (a ≫ c) := by rw [hac, Category.comp_id]
      _ = c := by rw [← Category.assoc, hba, Category.id_comp]
  obtain ⟨a, ha, _⟩ := (glue_sheaves_of_modules X I U hc).1 H F
    (fun i ↦ (χ i).hom) hχ
  obtain ⟨b, hb, _⟩ := (glue_sheaves_of_modules X I U hc).1 F H
    (fun i ↦ (χ i).inv) hχinv
  refine ⟨⟨a, b, ?_, ?_⟩⟩
  · apply (glue_sheaves_of_modules X I U hc).2.1
    intro i
    change (SheafOfModules.overFunctor (moduleRings X) (U i)).map (a ≫ b) = _
    rw [Functor.map_comp]
    change a.over (U i) ≫ b.over (U i) = _
    rw [ha i, hb i, Iso.hom_inv_id]
    exact ((SheafOfModules.overFunctor (moduleRings X) (U i)).map_id _).symm
  · apply (glue_sheaves_of_modules X I U hc).2.1
    intro i
    change (SheafOfModules.overFunctor (moduleRings X) (U i)).map (b ≫ a) = _
    rw [Functor.map_comp]
    change b.over (U i) ≫ a.over (U i) = _
    rw [hb i, ha i, Iso.inv_hom_id]
    exact ((SheafOfModules.overFunctor (moduleRings X) (U i)).map_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Finite-presentation modules on a ringed space have a set of isomorphism representatives.
Source: Stacks Project, Modules, Lemma 01BC, restricted using Definition 01BN
(blueprint: lem-weil-pbc-module-finite-presentation-representatives).

Proof:
1. For each open U, index local models by two natural numbers and a map between the
   corresponding finite free module sheaves on the localized site Over U. Take its cokernel.
   These indices form a type in universe u because morphism types do.
2. A finite presentation is locally a cokernel of a map between finite free modules.
   Reindex its generators and relations by lifted finite ordinals and transport the
   cokernel universal property. Thus each local restriction is isomorphic to a local model.
3. Apply lem-weil-pbc-module-local-model-gluing-data-set to these local families to obtain
   global modules Phi(d) and compatible local comparisons for each gluing datum d.
4. For a finitely presented F choose one presentation for each distinct member of its
   open cover. The local comparisons psi_U induce transitions psi_U followed by psi_V inverse;
   cancellation proves the cocycle. The comparison maps from Phi(d) to F agree on overlaps.
   Glue these maps and their inverses using lem-weil-pbc-glue-sheaves-of-modules; its local
   equality criterion shows that both composites are identities.
5. Restrict the small type of gluing data to those d for which Phi(d) has finite presentation.
   Isomorphism invariance of finite presentation shows that this family represents every F.
   The argument allows empty covers, zero ranks, and repeated opens in the original cover. -/
theorem exists_finitePresentation_representatives
    (X : RingedSpace.{u}) :
    ∃ (I : Type u) (G : I → SheafOfModules.{u} (moduleRings X)),
      (∀ i : I, (G i).IsFinitePresentation) ∧
      ∀ F : SheafOfModules.{u} (moduleRings X), F.IsFinitePresentation →
        ∃ i : I, Nonempty (F ≅ G i) := by
  classical
  let B := localModel X
  obtain ⟨_, Φ, θ, hθ⟩ := module_local_model_gluing_data_set X (localIndex X) B
  have represented (F : SheafOfModules.{u} (moduleRings X)) (hF : F.IsFinitePresentation) :
      ∃ d : ModuleLocalModelGluingData X (localIndex X) B, Nonempty (Φ d ≅ F) := by
    obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
    let _ := hq
    let C : Set (Opens X) := Set.range q.X
    have ex (U : C) : ∃ t : localIndex X U.val, Nonempty (B U.val t ≅ F.over U.val) := by
      obtain ⟨i, hi⟩ := U.property
      rw [← hi]
      exact presentation_localModel X (q.X i) (F.over (q.X i)) (q.presentation i)
    choose t ht using ex
    let ψ (U : C) : B U.val (t U) ≅ F.over U.val := (ht U).some
    clear_value ψ
    let e (U V : C) := modelTransition X F U.val V.val (ψ U) (ψ V)
    have he (U V : C) (W : Opens X) (hU : W ≤ U.val) (hV : W ≤ V.val) :
        (e U V).hom.val.app (op (Over.mk (homOfLE (le_inf hU hV)))) =
          (ψ U).hom.val.app (op (Over.mk (homOfLE hU))) ≫
            (ψ V).inv.val.app (op (Over.mk (homOfLE hV))) :=
      modelTransition_app X F U.val V.val (ψ U) (ψ V) W hU hV
    have hc : ⨆ U : C, U.val = ⊤ := by
      have h := (Opens.coversTop_iff X q.X).mp q.coversTop
      change ⨆ U : C, U.val = ⊤
      rw [iSup_subtype, iSup_range]
      exact h
    clear_value e
    let d : ModuleLocalModelGluingData X (localIndex X) B :=
      { cover := C
        isCover := hc
        label := t
        transition := e
        cocycle := by
          intro U V T W hU hV hT
          rw [he U T W hU hT, he U V W hU hV, he V T W hV hT]
          have hcancel :
              (ψ V).inv.val.app (op (Over.mk (homOfLE hV))) ≫
                (ψ V).hom.val.app (op (Over.mk (homOfLE hV))) = 𝟙 _ := by
            change ((ψ V).inv ≫ (ψ V).hom).val.app _ = _
            rw [Iso.inv_hom_id]
            rfl
          let a : (B U.val (t U)).val.obj (op (Over.mk (homOfLE hU))) ⟶
              F.val.obj (op W) := (ψ U).hom.val.app (op (Over.mk (homOfLE hU)))
          let b : F.val.obj (op W) ⟶
              (B V.val (t V)).val.obj (op (Over.mk (homOfLE hV))) :=
            (ψ V).inv.val.app (op (Over.mk (homOfLE hV)))
          let c : (B V.val (t V)).val.obj (op (Over.mk (homOfLE hV))) ⟶
              F.val.obj (op W) := (ψ V).hom.val.app (op (Over.mk (homOfLE hV)))
          let z : F.val.obj (op W) ⟶
              (B T.val (t T)).val.obj (op (Over.mk (homOfLE hT))) :=
            (ψ T).inv.val.app (op (Over.mk (homOfLE hT)))
          change a ≫ z = (a ≫ b) ≫ (c ≫ z)
          change b ≫ c = 𝟙 _ at hcancel
          rw [Category.assoc, ← Category.assoc b, hcancel, Category.id_comp] }
    let χ (U : C) : (Φ d).over U.val ≅ F.over U.val := θ d U ≪≫ ψ U
    have hχ (U V : C) (W : Opens X) (hU : W ≤ U.val) (hV : W ≤ V.val) :
        (χ U).hom.val.app (op (Over.mk (homOfLE hU))) =
          (χ V).hom.val.app (op (Over.mk (homOfLE hV))) := by
      have hh := hθ d U V W hU hV
      change (θ d U).hom.val.app (op (Over.mk (homOfLE hU))) ≫
          (e U V).hom.val.app (op (Over.mk (homOfLE (le_inf hU hV)))) =
        (θ d V).hom.val.app (op (Over.mk (homOfLE hV))) at hh
      rw [he U V W hU hV] at hh
      let a : (Φ d).val.obj (op W) ⟶ (B U.val (t U)).val.obj
          (op (Over.mk (homOfLE hU))) :=
        (θ d U).hom.val.app (op (Over.mk (homOfLE hU)))
      let b : (B U.val (t U)).val.obj (op (Over.mk (homOfLE hU))) ⟶
          F.val.obj (op W) := (ψ U).hom.val.app (op (Over.mk (homOfLE hU)))
      let c : F.val.obj (op W) ⟶
          (B V.val (t V)).val.obj (op (Over.mk (homOfLE hV))) :=
        (ψ V).inv.val.app (op (Over.mk (homOfLE hV)))
      let z : (B V.val (t V)).val.obj (op (Over.mk (homOfLE hV))) ⟶
          F.val.obj (op W) := (ψ V).hom.val.app (op (Over.mk (homOfLE hV)))
      let a' : (Φ d).val.obj (op W) ⟶
          (B V.val (t V)).val.obj (op (Over.mk (homOfLE hV))) :=
        (θ d V).hom.val.app (op (Over.mk (homOfLE hV)))
      change a ≫ (b ≫ c) = a' at hh
      have hcancel : c ≫ z = 𝟙 _ := by
        change ((ψ V).inv ≫ (ψ V).hom).val.app _ = _
        rw [Iso.inv_hom_id]
        rfl
      change a ≫ b = a' ≫ z
      rw [← hh, Category.assoc, Category.assoc, hcancel, Category.comp_id]
    exact ⟨d, iso_of_localComparisons X C Subtype.val hc (Φ d) F χ hχ⟩
  let D := ModuleLocalModelGluingData X (localIndex X) B
  let S := {d : D // (Φ d).IsFinitePresentation}
  refine ⟨S, fun i ↦ Φ i.val, fun i ↦ i.property, ?_⟩
  · intro F hF
    obtain ⟨d, ⟨e⟩⟩ := represented F hF
    have hd : (Φ d).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (moduleRings X)).prop_of_iso e.symm hF
    exact ⟨⟨d, hd⟩, ⟨e.symm⟩⟩

end AlgebraicGeometry.RingedSpace
