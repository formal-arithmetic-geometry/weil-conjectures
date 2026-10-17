/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CofilteredLimitStageDescent

/-!
# Descent of étale schemes, morphisms and equalities to a stage of a cofiltered limit

Let `D : I ⥤ Scheme` be a cofiltered inverse system of quasi-compact quasi-separated schemes with
affine transition maps and limit cone `c`. We record, in the language of the slice categories
`Over (D.obj i)` and the base change functors `Over.pullback`, that

* quasi-compact quasi-separated étale `c.pt`-schemes descend to a stage
  (`AlgebraicGeometry.exists_isQcqsEtale_overPullback_iso`);
* morphisms between base changes of finitely presented stage schemes eventually descend
  (`AlgebraicGeometry.stageEventually_exists_overPullback_hom`);
* equalities between morphisms eventually descend
  (`AlgebraicGeometry.stageEventually_overPullback_map_eq`).

"Eventually" is made precise by `AlgebraicGeometry.StageEventually`: a property of the morphisms
`j ⟶ i` holds eventually if it holds for all morphisms factoring through a fixed one.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An object of `Over X` whose structure morphism is étale, locally of finite presentation,
quasi-compact and quasi-separated. -/
abbrev IsQcqsEtale {X : Scheme.{u}} (U : Over X) : Prop :=
  Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧ QuasiCompact U.hom ∧ QuasiSeparated U.hom

lemma IsQcqsEtale.overPullback {X Y : Scheme.{u}} {U : Over X} (hU : IsQcqsEtale U)
    (f : Y ⟶ X) : IsQcqsEtale ((Over.pullback f).obj U) := by
  obtain ⟨_, _, _, _⟩ := hU
  exact ⟨by dsimp; infer_instance, by dsimp; infer_instance, by dsimp; infer_instance,
    by dsimp; infer_instance⟩

section StageEventually

variable {I : Type u} [Category.{u} I]

/-- A property `Q` of morphisms `j ⟶ i` holds *eventually* if there is `h : j ⟶ i` such that
`Q (g ≫ h)` holds for every `g : k ⟶ j`. -/
def StageEventually (i : I) (Q : ∀ ⦃j : I⦄, (j ⟶ i) → Prop) : Prop :=
  ∃ (j : I) (h : j ⟶ i), ∀ ⦃k : I⦄ (g : k ⟶ j), Q (g ≫ h)

namespace StageEventually

variable {i : I} {Q Q' : ∀ ⦃j : I⦄, (j ⟶ i) → Prop}

lemma exists_hom (hQ : StageEventually i Q) : ∃ (j : I) (h : j ⟶ i), Q h := by
  obtain ⟨j, h, H⟩ := hQ
  exact ⟨j, h, by simpa using H (𝟙 j)⟩

lemma of_forall (H : ∀ ⦃j : I⦄ (h : j ⟶ i), Q h) : StageEventually i Q :=
  ⟨i, 𝟙 i, fun _ _ ↦ H _⟩

lemma mono (hQ : StageEventually i Q) (H : ∀ ⦃j : I⦄ (h : j ⟶ i), Q h → Q' h) :
    StageEventually i Q' := by
  obtain ⟨j, h, hj⟩ := hQ
  exact ⟨j, h, fun _ g ↦ H _ (hj g)⟩

/-- A property which holds at some stage and is stable under further restriction holds
eventually. -/
lemma of_exists (H : ∃ (j : I) (h : j ⟶ i), Q h)
    (hmono : ∀ ⦃j k : I⦄ (h : j ⟶ i) (g : k ⟶ j), Q h → Q (g ≫ h)) : StageEventually i Q := by
  obtain ⟨j, h, hQ⟩ := H
  exact ⟨j, h, fun _ g ↦ hmono h g hQ⟩

variable [IsCofiltered I]

lemma and (hQ : StageEventually i Q) (hQ' : StageEventually i Q') :
    StageEventually i (fun _ h ↦ Q h ∧ Q' h) := by
  obtain ⟨j, h, H⟩ := hQ
  obtain ⟨j', h', H'⟩ := hQ'
  obtain ⟨k, g, g', w⟩ := IsCofiltered.cospan h h'
  refine ⟨k, g ≫ h, fun l e ↦ ⟨?_, ?_⟩⟩
  · simpa using H (e ≫ g)
  · simpa [w] using H' (e ≫ g')

lemma finset_forall {ι : Type*} (s : Finset ι) {Q : ι → ∀ ⦃j : I⦄, (j ⟶ i) → Prop}
    (hQ : ∀ a ∈ s, StageEventually i (Q a)) :
    StageEventually i (fun _ h ↦ ∀ a ∈ s, Q a h) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact of_forall (by simp)
  | insert a s _ ih =>
    refine ((hQ a (by simp)).and (ih fun b hb ↦ hQ b (by simp [hb]))).mono ?_
    rintro _ h ⟨h₁, h₂⟩ b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    exacts [h₁, h₂ b hb]

lemma finite_forall {ι : Type*} [Finite ι] {Q : ι → ∀ ⦃j : I⦄, (j ⟶ i) → Prop}
    (hQ : ∀ a, StageEventually i (Q a)) :
    StageEventually i (fun _ h ↦ ∀ a, Q a h) := by
  have := Fintype.ofFinite ι
  exact (finset_forall Finset.univ (Q := Q) (fun a _ ↦ hQ a)).mono (by simp)

end StageEventually

end StageEventually

section Descent

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The comparison between base change along a transition map followed by base change to the
limit, and base change to the limit. -/
noncomputable def overPullbackStageIso {i j : I} (h : j ⟶ i) :
    Over.pullback (D.map h) ⋙ Over.pullback (c.π.app j) ≅ Over.pullback (c.π.app i) :=
  (Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))

omit [Category.{u} I] in
set_option linter.flexible false in
private lemma pullbackComp_eqToHom_left_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (f' : X ⟶ Z) (hf : f ≫ g = f') (U : Over Z) :
    ((Over.pullbackComp f g).inv.app U ≫
        (eqToHom (congrArg (fun k : X ⟶ Z ↦ Over.pullback k) hf)).app U).left ≫
      pullback.fst U.hom f' = pullback.fst _ f ≫ pullback.fst U.hom g := by
  subst hf
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id]
  simp [Over.pullbackComp, Over.mapComp, conjugateIsoEquiv, conjugateEquiv]
  exact Category.id_comp (pullback.fst (pullback.snd U.hom g) f ≫ pullback.fst U.hom g)

@[reassoc (attr := simp)]
lemma overPullbackStageIso_hom_app_left_fst {i j : I} (h : j ⟶ i) (U : Over (D.obj i)) :
    ((overPullbackStageIso D c h).hom.app U).left ≫ pullback.fst U.hom (c.π.app i) =
      pullback.fst _ (c.π.app j) ≫ pullback.fst U.hom (D.map h) :=
  pullbackComp_eqToHom_left_fst _ _ _ (c.w h) U

@[reassoc (attr := simp)]
lemma overPullbackStageIso_hom_app_left_snd {i j : I} (h : j ⟶ i) (U : Over (D.obj i)) :
    ((overPullbackStageIso D c h).hom.app U).left ≫ pullback.snd U.hom (c.π.app i) =
      pullback.snd _ (c.π.app j) :=
  Over.w ((overPullbackStageIso D c h).hom.app U)

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {c} (hc : IsLimit c)

include hc in
/-- **Quasi-compact quasi-separated étale schemes descend** to a stage of a cofiltered limit
(Stacks Project Tags 01ZM and 07RP). -/
theorem exists_isQcqsEtale_overPullback_iso (U : Over c.pt) (hU : IsQcqsEtale U) :
    ∃ (i : I) (Ui : Over (D.obj i)), IsQcqsEtale Ui ∧
      Nonempty ((Over.pullback (c.π.app i)).obj Ui ≅ U) := by
  obtain ⟨_, _, _, _⟩ := hU
  obtain ⟨i, Y, p, _, _, _, t, hP⟩ := Scheme.exists_isPullback_of_finitePresentation hc U.hom
  have hp : Etale (pullback.snd p (c.π.app i)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale hP.isoPullback.hom,
      hP.isoPullback_hom_snd]
    infer_instance
  obtain ⟨j, h, _⟩ := Etale.exists_stage_of_isLimit D c hc i p hp
  refine ⟨j, Over.mk (pullback.snd p (D.map h)),
    ⟨(inferInstance : Etale (pullback.snd p (D.map h))),
      (inferInstance : LocallyOfFinitePresentation (pullback.snd p (D.map h))),
      (inferInstance : QuasiCompact (pullback.snd p (D.map h))),
      (inferInstance : QuasiSeparated (pullback.snd p (D.map h)))⟩, ⟨?_⟩⟩
  refine Over.isoMk (pullbackLeftPullbackSndIso p (D.map h) (c.π.app j) ≪≫
    pullback.congrHom rfl (c.w h) ≪≫ hP.isoPullback.symm) ?_
  simp

include hc in
/-- **Morphisms descend eventually** (Stacks Project Tag 01ZM): a morphism between the base
changes to the limit of two finitely presented schemes over a stage `D i` is, for every
sufficiently late `h : j ⟶ i`, the base change of a morphism over `D j`. -/
theorem stageEventually_exists_overPullback_hom {i : I} (U V : Over (D.obj i))
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom] [QuasiSeparated U.hom]
    [LocallyOfFinitePresentation V.hom] [QuasiCompact V.hom] [QuasiSeparated V.hom]
    (ψ : (Over.pullback (c.π.app i)).obj U ⟶ (Over.pullback (c.π.app i)).obj V) :
    StageEventually i (fun j h ↦ ∃ φ : (Over.pullback (D.map h)).obj U ⟶
        (Over.pullback (D.map h)).obj V,
      (Over.pullback (c.π.app j)).map φ ≫ (overPullbackStageIso D c h).hom.app V =
        (overPullbackStageIso D c h).hom.app U ≫ ψ) := by
  have hψ : (ψ.left ≫ pullback.fst V.hom (c.π.app i)) ≫ V.hom =
      pullback.fst U.hom (c.π.app i) ≫ U.hom := by
    have := Over.w ψ
    simp only [Functor.const_obj_obj, Over.pullback_obj_left,
      Over.pullback_obj_hom] at this
    rw [Category.assoc, pullback.condition, ← Category.assoc, this, pullback.condition]
  obtain ⟨j, f, ψj, hψj, hψj'⟩ := Scheme.exists_pullback_hom_of_isLimit hc U.hom V.hom _ hψ
  refine ⟨j, f, fun k g ↦ ?_⟩
  let m : pullback U.hom (D.map (g ≫ f)) ⟶ pullback U.hom (D.map f) :=
    pullback.map _ _ _ _ (𝟙 _) (D.map g) (𝟙 _) (by simp) (by simp)
  refine ⟨Over.homMk (pullback.lift (m ≫ ψj) (pullback.snd _ _) ?_) ?_, ?_⟩
  · simp [m, hψj, pullback.condition]
  · simp
  · ext : 1
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, overPullbackStageIso_hom_app_left_fst,
        Over.pullback_map_left, pullback.lift_fst_assoc, Over.homMk_left, pullback.lift_fst]
      rw [← hψj']
      simp only [m, ← Category.assoc]
      refine congrArg (· ≫ ψj) ?_
      apply pullback.hom_ext
      · simp
      · simp [pullback.condition_assoc]
    · have hw : ψ.left ≫ pullback.snd V.hom (c.π.app i) = pullback.snd U.hom (c.π.app i) :=
        Over.w ψ
      simp [hw]

include hc in
/-- **Equalities of morphisms descend eventually** (Stacks Project Tag 01ZM). -/
theorem stageEventually_overPullback_map_eq {i : I} (U V : Over (D.obj i))
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom] [QuasiSeparated U.hom]
    [LocallyOfFinitePresentation V.hom] [QuasiCompact V.hom] [QuasiSeparated V.hom]
    (ψ χ : U ⟶ V)
    (h : (Over.pullback (c.π.app i)).map ψ = (Over.pullback (c.π.app i)).map χ) :
    StageEventually i (fun _ h ↦
      (Over.pullback (D.map h)).map ψ = (Over.pullback (D.map h)).map χ) := by
  obtain ⟨j, f, hf⟩ := Scheme.exists_pullback_fst_comp_eq_of_isLimit hc U.hom V.hom ψ.left
    χ.left (Over.w ψ) (Over.w χ) (by
      have := congrArg (fun φ ↦ φ.left ≫ pullback.fst V.hom (c.π.app i)) h
      simpa using this)
  refine ⟨j, f, fun k g ↦ ?_⟩
  ext : 1
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    have e : pullback.fst U.hom (D.map (g ≫ f)) =
        pullback.map _ _ _ _ (𝟙 _) (D.map g) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst U.hom (D.map f) := by simp
    rw [e]
    simp only [Category.assoc, hf]
  · simp

end Descent

end AlgebraicGeometry
