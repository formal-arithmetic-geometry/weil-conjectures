/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.Topology.GlueSheavesOfModules
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistGluing

/-!
# Existence and uniqueness of twists on the projective line

Source: Weil conjectures blueprint, `sec-picard-framework`, `sk-thm-picard-coherence`,
node `lem-sc-p1-twist-exists`, order 636 (blueprint: lem-sc-p1-twist-exists).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

private noncomputable def generatorHom {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U :=
  (M.over U).unitHomEquiv.symm <| (M.over U).val.sectionsMk
    (fun V ↦ M.presheaf.map V.unop.hom.op s) (by
      intro V W f
      change M.presheaf.map f.unop.left.op (M.presheaf.map V.unop.hom.op s) =
        M.presheaf.map W.unop.hom.op s
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← CategoryTheory.op_comp]
      congr 2
)

private noncomputable def generatorIso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U))
    (hs : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE hV).op s) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U := by
  let f := generatorHom M U s
  let e : (SheafOfModules.unit (X.ringCatSheaf.over U)).val ≅ (M.over U).val :=
    PresheafOfModules.isoMk (fun V ↦
      (LinearEquiv.ofBijective (f.val.app V).hom
        (hs V.unop.left (leOfHom V.unop.hom))).toModuleIso) (by
          intro V W g
          exact f.val.naturality g)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso e
private lemma generatorIso_hom_app {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U))
    (hs : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE hV).op s)
    (V : Over U) (a : Γ(X, V.left)) :
    (generatorIso M U s hs).hom.val.app (Opposite.op V) a =
      a • M.presheaf.map V.hom.op s := rfl

private lemma chart_cover (S : Scheme.{u}) :
    ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩ ⊔
      ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) S ⟨1⟩ = ⊤ := by
  have h := ProjectiveSpace.iSup_standardOpen (ULift.{u} (Fin 2)) S
  apply top_le_iff.mp
  rw [← h]
  apply iSup_le
  rintro ⟨i⟩
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private lemma twist_invertible {S : Scheme.{u}} {d : ℤ}
    {L : (ProjectiveLine S).Modules} (T : TwistData S d L) :
    Scheme.Modules.IsInvertible L := by
  refine ⟨fun x ↦ ?_⟩
  have hx : x ∈ ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩ ⊔
      ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) S ⟨1⟩ := by
    rw [chart_cover]
    trivial
  rcases hx with hx | hx
  · let U := ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩
    let e := generatorIso L U T.g₀ T.bijective_smul_g₀
    refine ⟨U, hx, ⟨?_⟩⟩
    exact ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app L) ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app L).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso e.symm ≪≫
      (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
  · let U := ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) S ⟨1⟩
    let e := generatorIso L U T.g₁ T.bijective_smul_g₁
    refine ⟨U, hx, ⟨?_⟩⟩
    exact ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app L) ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app L).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso e.symm ≪≫
      (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
private lemma over_hom_ext_generator {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens}
    (s : Γ(M, U))
    (hs : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Surjective fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE hV).op s)
    (f g : M ⟶ N) (h : f.app U s = g.app U s) : f.over U = g.over U := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  obtain ⟨a, rfl⟩ := hs V.unop.left (leOfHom V.unop.hom) x
  change f.app V.unop.left (a • M.presheaf.map V.unop.hom.op s) =
    g.app V.unop.left (a • M.presheaf.map V.unop.hom.op s)
  simp only [Scheme.Modules.Hom.app_smul]
  congr 1
  change f.val.app (Opposite.op V.unop.left) (M.val.map V.unop.hom.op s) =
    g.val.app (Opposite.op V.unop.left) (M.val.map V.unop.hom.op s)
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  exact congrArg (N.presheaf.map V.unop.hom.op) h

private lemma twist_hom_ext {S : Scheme.{u}} {d : ℤ}
    {L N : (ProjectiveLine S).Modules} (T : TwistData S d L) (f g : L ⟶ N)
    (h₀ : f.app (ProjectiveSpace.standardOpen _ S ⟨0⟩) T.g₀ =
      g.app (ProjectiveSpace.standardOpen _ S ⟨0⟩) T.g₀)
    (h₁ : f.app (ProjectiveSpace.standardOpen _ S ⟨1⟩) T.g₁ =
      g.app (ProjectiveSpace.standardOpen _ S ⟨1⟩) T.g₁) : f = g := by
  let U : Bool → (ProjectiveLine S).Opens := fun b ↦
    match b with
    | false => ProjectiveSpace.standardOpen _ S ⟨0⟩
    | true => ProjectiveSpace.standardOpen _ S ⟨1⟩
  have hcover : ⨆ b, U b = ⊤ := by
    apply le_antisymm le_top
    rw [← chart_cover S]
    exact sup_le (le_iSup_of_le false le_rfl) (le_iSup_of_le true le_rfl)
  apply (glue_sheaves_of_modules (ProjectiveLine S).toRingedSpace Bool U hcover).2.1 L N f g
  intro b
  cases b
  · exact over_hom_ext_generator T.g₀ (fun V hV ↦ (T.bijective_smul_g₀ V hV).2) f g h₀
  · exact over_hom_ext_generator T.g₁ (fun V hV ↦ (T.bijective_smul_g₁ V hV).2) f g h₁
private noncomputable def localMap {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U))
    (hs : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE hV).op s)
    (ht : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • N.presheaf.map (homOfLE hV).op t) :
    M.over U ⟶ N.over U :=
  (generatorIso M U s hs).inv ≫ (generatorIso N U t ht).hom

private lemma localMap_apply {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U))
    (hs : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE hV).op s)
    (ht : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • N.presheaf.map (homOfLE hV).op t)
    (V : Over U) (a : Γ(X, V.left)) :
    (localMap M N U s t hs ht).val.app (Opposite.op V) (a • M.presheaf.map V.hom.op s) =
      a • N.presheaf.map V.hom.op t := by
  rw [← generatorIso_hom_app M U s hs]
  change ((generatorIso M U s hs).hom ≫
    (generatorIso M U s hs).inv ≫ (generatorIso N U t ht).hom).val.app (Opposite.op V) a = _
  rw [Iso.hom_inv_id_assoc]
  rfl
private lemma localMap_apply_subopen {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U))
    (hs : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE hV).op s)
    (ht : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • N.presheaf.map (homOfLE hV).op t)
    (V : X.Opens) (hV : V ≤ U) (a : Γ(X, V)) :
    (localMap M N U s t hs ht).val.app (Opposite.op (Over.mk (homOfLE hV)))
        (a • M.presheaf.map (homOfLE hV).op s) =
      a • N.presheaf.map (homOfLE hV).op t :=
  localMap_apply M N U s t hs ht (Over.mk (homOfLE hV)) a

private lemma twist_relation {S : Scheme.{u}} {d : ℤ}
    {L : (ProjectiveLine S).Modules} (T : TwistData S d L)
    (W : (ProjectiveLine S).Opens)
    (h₀ : W ≤ ProjectiveSpace.standardOpen _ S ⟨0⟩)
    (h₁ : W ≤ ProjectiveSpace.standardOpen _ S ⟨1⟩) :
    L.presheaf.map (homOfLE h₀).op T.g₀ =
      (ProjectiveLine S).presheaf.map (homOfLE (le_inf h₀ h₁)).op
        (ProjectiveSpace.transitionUnit (ULift.{u} (Fin 2)) S d ⟨0⟩ ⟨1⟩).val •
      L.presheaf.map (homOfLE h₁).op T.g₁ := by
  have h := congrArg (L.presheaf.map (homOfLE (le_inf h₀ h₁)).op) T.map_g₀
  rw [Scheme.Modules.map_smul] at h
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← CategoryTheory.op_comp, homOfLE_comp] using h

set_option backward.isDefEq.respectTransparency false in
private theorem exists_twist_hom {S : Scheme.{u}} {d : ℤ}
    {L N : (ProjectiveLine S).Modules} (T : TwistData S d L) (T' : TwistData S d N) :
    ∃ f : L ⟶ N,
      f.app (ProjectiveSpace.standardOpen _ S ⟨0⟩) T.g₀ = T'.g₀ ∧
      f.app (ProjectiveSpace.standardOpen _ S ⟨1⟩) T.g₁ = T'.g₁ := by
  let U : Bool → (ProjectiveLine S).Opens := fun b ↦
    match b with
    | false => ProjectiveSpace.standardOpen _ S ⟨0⟩
    | true => ProjectiveSpace.standardOpen _ S ⟨1⟩
  have hcover : ⨆ b, U b = ⊤ := by
    apply le_antisymm le_top
    rw [← chart_cover S]
    exact sup_le (le_iSup_of_le false le_rfl) (le_iSup_of_le true le_rfl)
  let φ : ∀ b, L.over (U b) ⟶ N.over (U b) := fun b ↦ by
    cases b
    · exact localMap L N _ T.g₀ T'.g₀ T.bijective_smul_g₀ T'.bijective_smul_g₀
    · exact localMap L N _ T.g₁ T'.g₁ T.bijective_smul_g₁ T'.bijective_smul_g₁
  have hagree : ∀ (i j : Bool) (W : (ProjectiveLine S).Opens)
      (hi : W ≤ U i) (hj : W ≤ U j),
      (φ i).val.app (Opposite.op (Over.mk (homOfLE hi))) =
        (φ j).val.app (Opposite.op (Over.mk (homOfLE hj))) := by
    have h01 : ∀ (W : (ProjectiveLine S).Opens)
        (h₀ : W ≤ U false) (h₁ : W ≤ U true),
        (φ false).val.app (Opposite.op (Over.mk (homOfLE h₀))) =
          (φ true).val.app (Opposite.op (Over.mk (homOfLE h₁))) := by
      intro W h₀ h₁
      dsimp only [U] at h₀ h₁
      dsimp only [φ, U]
      ext x
      obtain ⟨a, rfl⟩ := (T.bijective_smul_g₀ W h₀).2 x
      change (localMap L N _ T.g₀ T'.g₀ T.bijective_smul_g₀
        T'.bijective_smul_g₀).val.app (Opposite.op (Over.mk (homOfLE h₀)))
          (a • L.presheaf.map (homOfLE h₀).op T.g₀) =
        (localMap L N _ T.g₁ T'.g₁ T.bijective_smul_g₁
          T'.bijective_smul_g₁).val.app (Opposite.op (Over.mk (homOfLE h₁)))
            (a • L.presheaf.map (homOfLE h₀).op T.g₀)
      have hmap₀ := localMap_apply_subopen L N _ T.g₀ T'.g₀
        T.bijective_smul_g₀ T'.bijective_smul_g₀ W h₀ a
      refine hmap₀.trans ?_
      rw [twist_relation T W h₀ h₁, smul_smul]
      have hmap₁ := localMap_apply_subopen L N _ T.g₁ T'.g₁
        T.bijective_smul_g₁ T'.bijective_smul_g₁ W h₁
        (a * (ProjectiveLine S).presheaf.map (homOfLE (le_inf h₀ h₁)).op
          (ProjectiveSpace.transitionUnit (ULift.{u} (Fin 2)) S d ⟨0⟩ ⟨1⟩).val)
      rw [twist_relation T' W h₀ h₁, smul_smul]
      exact hmap₁.symm
    intro i j W hi hj
    cases i <;> cases j
    · rfl
    · exact h01 W hi hj
    · exact (h01 W hj hi).symm
    · rfl
  obtain ⟨f, hf, _⟩ :=
    (glue_sheaves_of_modules (ProjectiveLine S).toRingedSpace Bool U hcover).1 L N φ hagree
  refine ⟨f, ?_, ?_⟩
  · have h := congrArg (fun p ↦ p.val.app (Opposite.op (Over.mk (𝟙 (U false))))) (hf false)
    have h' := ConcreteCategory.congr_hom h T.g₀
    have hmap := localMap_apply_subopen L N _ T.g₀ T'.g₀
      T.bijective_smul_g₀ T'.bijective_smul_g₀
      (ProjectiveSpace.standardOpen _ S ⟨0⟩) le_rfl 1
    dsimp only [φ, U] at h'
    exact h'.trans (by simpa using hmap)
  · have h := congrArg (fun p ↦ p.val.app (Opposite.op (Over.mk (𝟙 (U true))))) (hf true)
    have h' := ConcreteCategory.congr_hom h T.g₁
    have hmap := localMap_apply_subopen L N _ T.g₁ T'.g₁
      T.bijective_smul_g₁ T'.bijective_smul_g₁
      (ProjectiveSpace.standardOpen _ S ⟨1⟩) le_rfl 1
    dsimp only [φ, U] at h'
    exact h'.trans (by simpa using hmap)

/-- The twist O(d) exists, is invertible, and is unique up to unique isomorphism preserving
its two standard generators.
Source: Weil conjectures blueprint, `lem-sc-p1-twist-exists`, order 636.
Proof: take free rank-one modules on the two standard opens. On their overlap send the
first generator to t^(-d) times the second; this is an isomorphism since t is a unit
(def-sc-p1-standard). Set the self-transition maps to identities. The cocycle identities
reduce to t^d * t^(-d) = 1 and t^(-d) * t^d = 1. Glue the modules and their trivializations
using clause (2) of lem-weil-pbc-glue-sheaves-of-modules. Quasi-coherence is local and each
chart is free of rank one, so the glued module is invertible (def-sc-invertible-module).
For another twist, the generator-preserving local maps agree on the overlap. Clause (1)
of lem-weil-pbc-glue-sheaves-of-modules glues them uniquely. Glue the inverse local maps
as well to obtain a unique compatible isomorphism.
(blueprint: lem-sc-p1-twist-exists). -/
theorem exists_twistData_unique_iso (k : Type u) [Field k] (d : ℤ) :
    ∃ (L : (ProjectiveLine (Spec (.of k))).Modules)
      (T : TwistData (Spec (.of k)) d L),
      Scheme.Modules.IsInvertible L ∧
        ∀ (L' : (ProjectiveLine (Spec (.of k))).Modules)
          (T' : TwistData (Spec (.of k)) d L'),
          ∃! e : L ≅ L',
            e.hom.app (ProjectiveSpace.standardOpen _ (Spec (.of k)) ⟨0⟩) T.g₀ = T'.g₀ ∧
            e.hom.app (ProjectiveSpace.standardOpen _ (Spec (.of k)) ⟨1⟩) T.g₁ = T'.g₁ := by
  obtain ⟨L, ⟨T⟩⟩ := exists_twistData k d
  refine ⟨L, T, twist_invertible T, ?_⟩
  intro L' T'
  obtain ⟨f, hf₀, hf₁⟩ := exists_twist_hom T T'
  obtain ⟨g, hg₀, hg₁⟩ := exists_twist_hom T' T
  let e : L ≅ L' :=
    { hom := f
      inv := g
      hom_inv_id := twist_hom_ext T (f ≫ g) (𝟙 L)
        (by simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
          hf₀, hg₀, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply])
        (by simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
          hf₁, hg₁, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply])
      inv_hom_id := twist_hom_ext T' (g ≫ f) (𝟙 L')
        (by simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
          hg₀, hf₀, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply])
        (by simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
          hg₁, hf₁, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]) }
  refine ⟨e, ⟨hf₀, hf₁⟩, ?_⟩
  intro e' he'
  apply Iso.ext
  exact twist_hom_ext T e'.hom f (he'.1.trans hf₀.symm) (he'.2.trans hf₁.symm)

end AlgebraicGeometry.ProjectiveLine
