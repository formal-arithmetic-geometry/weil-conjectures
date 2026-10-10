/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.BaseChange
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Finite-stage models of the same scheme become isomorphic

Two finite-stage models of the same scheme over a cofiltered limit of quasi-compact
quasi-separated schemes become isomorphic at a later stage
(`AlgebraicGeometry.exists_iso_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section FinitePresentationDescent

/-!
### Descending a scheme of finite presentation to a finite stage

Let `{Dⱼ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps and let `X` be of finite presentation over `lim Dⱼ`. Then `X` is the base change
of a scheme of finite presentation over one of the stages (Stacks Project Tag 01ZM,
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`). If `X` is moreover
separated over `lim Dⱼ`, the finite-stage model can be chosen separated (Stacks Project
Tag 01ZQ, `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`);
this rests on the fact that a finitely presented morphism whose base change to the limit is a
closed immersion is a closed immersion at a finite stage
(`AlgebraicGeometry.Scheme.exists_isClosedImmersion_overPullbackMap`), applied to the diagonal
of the descended model.

The affine case is
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`. It
covers an affine `X` lying over an affine open `V` of a stage, by base changing the whole system
to `V` (`AlgebraicGeometry.DescendsToStage.of_isAffine`). The general case is an induction over
a finite cover of `X` by such affine opens: at each step one has to glue two
finite-stage models along a descent of their intersection. The gluing data is produced by
`AlgebraicGeometry.exists_descendsAtWithOpen` (a quasi-compact open descends) and
`AlgebraicGeometry.exists_iso_of_isPullback` (two finite-stage models of the same scheme become
isomorphic at a later stage), the gluing itself is the pushout of two open immersions of
`AlgebraicGeometry.pushoutOpensDesc`, and that the glued morphism is again cartesian is
`AlgebraicGeometry.isPullback_of_opensRange_sup_eq_top`.
-/

section Descent

set_option backward.defeqAttrib.useBackward true

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

instance baseChange_compactSpace {k k' : I} (f : k' ⟶ k) {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [CompactSpace Y] : CompactSpace ↥(pullback p (D.map f)) :=
  have : IsAffineHom (pullback.fst p (D.map f)) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (pullback.fst p (D.map f)) := inferInstance
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst p (D.map f))

instance baseChange_quasiSeparatedSpace {k k' : I} (f : k' ⟶ k) {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [QuasiSeparatedSpace Y] : QuasiSeparatedSpace ↥(pullback p (D.map f)) :=
  have : IsAffineHom (pullback.fst p (D.map f)) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst p (D.map f)) := inferInstance
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (D.map f))

instance baseChangeDiagram_compactSpace {k : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [CompactSpace Y] (j : Over k) : CompactSpace ↥((baseChangeDiagram D p).obj j) :=
  inferInstanceAs (CompactSpace ↥(pullback p (D.map j.hom)))

instance baseChangeDiagram_quasiSeparatedSpace {k : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [QuasiSeparatedSpace Y] (j : Over k) : QuasiSeparatedSpace ↥((baseChangeDiagram D p).obj j) :=
  inferInstanceAs (QuasiSeparatedSpace ↥(pullback p (D.map j.hom)))

variable (D) in
/-- (Implementation) The structure morphism of the base changed diagram to the stage `i`. -/
@[simps] noncomputable def baseChangeDiagramStructure {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i) :
    baseChangeDiagram D p ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app j := pullback.fst _ _ ≫ p

include hc in
/-- (Implementation) **Two finite-stage models of a scheme over the limit become isomorphic at
a later stage.** -/
lemma exists_iso_of_isPullback {X : Scheme.{u}} {g : X ⟶ c.pt} {k : I}
    {Y₁ Y₂ : Scheme.{u}} {p₁ : Y₁ ⟶ D.obj k} {p₂ : Y₂ ⟶ D.obj k} {h₁ : X ⟶ Y₁} {h₂ : X ⟶ Y₂}
    [LocallyOfFinitePresentation p₁] [LocallyOfFinitePresentation p₂]
    [CompactSpace Y₁] [QuasiSeparatedSpace Y₁] [CompactSpace Y₂] [QuasiSeparatedSpace Y₂]
    (H₁ : IsPullback h₁ g p₁ (c.π.app k)) (H₂ : IsPullback h₂ g p₂ (c.π.app k)) :
    ∃ (k' : I) (f : k' ⟶ k), ∀ {Y₁' Y₂' : Scheme.{u}} {p₁' : Y₁' ⟶ D.obj k'} {q₁ : Y₁' ⟶ Y₁}
      {p₂' : Y₂' ⟶ D.obj k'} {q₂ : Y₂' ⟶ Y₂} {h₁' : X ⟶ Y₁'} {h₂' : X ⟶ Y₂'},
      IsPullback q₁ p₁' p₁ (D.map f) → h₁' ≫ q₁ = h₁ → h₁' ≫ p₁' = g ≫ c.π.app k' →
      IsPullback q₂ p₂' p₂ (D.map f) → h₂' ≫ q₂ = h₂ → h₂' ≫ p₂' = g ≫ c.π.app k' →
      ∃ e : Y₁' ≅ Y₂', e.hom ≫ p₂' = p₁' ∧ h₁' ≫ e.hom = h₂' := by
  classical
  have hi₁fst : H₁.isoPullback.hom ≫ pullback.fst p₁ (c.π.app k) = h₁ :=
    IsPullback.isoPullback_hom_fst _
  have hi₁snd : H₁.isoPullback.hom ≫ pullback.snd p₁ (c.π.app k) = g :=
    IsPullback.isoPullback_hom_snd _
  have hi₂fst : H₂.isoPullback.hom ≫ pullback.fst p₂ (c.π.app k) = h₂ :=
    IsPullback.isoPullback_hom_fst _
  have hi₂snd : H₂.isoPullback.hom ≫ pullback.snd p₂ (c.π.app k) = g :=
    IsPullback.isoPullback_hom_snd _
  have hinvg₁ : H₁.isoPullback.inv ≫ g = pullback.snd p₁ (c.π.app k) := by
    rw [Iso.inv_comp_eq, hi₁snd]
  have hinvg₂ : H₂.isoPullback.inv ≫ g = pullback.snd p₂ (c.π.app k) := by
    rw [Iso.inv_comp_eq, hi₂snd]
  -- descend the two comparison morphisms
  obtain ⟨j₁, u₁, hu₁a, hu₁t⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (baseChangeDiagram D p₁) (baseChangeDiagramStructure D p₁) p₂ (baseChangeCone D c p₁)
      (isLimitBaseChangeCone D c p₁ hc) (H₁.isoPullback.inv ≫ h₂) (by
    ext j
    change ((baseChangeCone D c p₁).π.app j ≫ pullback.fst p₁ (D.map j.hom)) ≫ p₁ =
      (H₁.isoPullback.inv ≫ h₂) ≫ p₂
    rw [baseChangeCone_π_app_fst, Category.assoc, H₂.w, ← Category.assoc, hinvg₁]
    exact pullback.condition)
  obtain ⟨j₂, u₂, hu₂a, hu₂t⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (baseChangeDiagram D p₂) (baseChangeDiagramStructure D p₂) p₁ (baseChangeCone D c p₂)
      (isLimitBaseChangeCone D c p₂ hc) (H₂.isoPullback.inv ≫ h₁) (by
    ext j
    change ((baseChangeCone D c p₂).π.app j ≫ pullback.fst p₂ (D.map j.hom)) ≫ p₂ =
      (H₂.isoPullback.inv ≫ h₁) ≫ p₁
    rw [baseChangeCone_π_app_fst, Category.assoc, H₁.w, ← Category.assoc, hinvg₂]
    exact pullback.condition)
  -- move them to a common stage
  set j₃ := IsCofiltered.min j₁ j₂ with hj₃
  set m₁ : j₃ ⟶ j₁ := IsCofiltered.minToLeft j₁ j₂ with hm₁
  set m₂ : j₃ ⟶ j₂ := IsCofiltered.minToRight j₁ j₂ with hm₂
  have hu₁t' : u₁ ≫ p₂ = pullback.fst p₁ (D.map j₁.hom) ≫ p₁ := hu₁t
  have hu₂t' : u₂ ≫ p₁ = pullback.fst p₂ (D.map j₂.hom) ≫ p₂ := hu₂t
  set v₁ : (baseChangeDiagram D p₁).obj j₃ ⟶ (baseChangeDiagram D p₂).obj j₃ :=
    pullback.lift ((baseChangeDiagram D p₁).map m₁ ≫ u₁) (pullback.snd p₁ (D.map j₃.hom))
      (by rw [Category.assoc, hu₁t', baseChangeDiagram_map_fst_assoc]
          exact pullback.condition) with hv₁def
  set v₂ : (baseChangeDiagram D p₂).obj j₃ ⟶ (baseChangeDiagram D p₁).obj j₃ :=
    pullback.lift ((baseChangeDiagram D p₂).map m₂ ≫ u₂) (pullback.snd p₂ (D.map j₃.hom))
      (by rw [Category.assoc, hu₂t', baseChangeDiagram_map_fst_assoc]
          exact pullback.condition) with hv₂def
  have hv₁fst : v₁ ≫ pullback.fst p₂ (D.map j₃.hom) = (baseChangeDiagram D p₁).map m₁ ≫ u₁ :=
    pullback.lift_fst ..
  have hv₁snd : v₁ ≫ pullback.snd p₂ (D.map j₃.hom) = pullback.snd p₁ (D.map j₃.hom) :=
    pullback.lift_snd ..
  have hv₂fst : v₂ ≫ pullback.fst p₁ (D.map j₃.hom) = (baseChangeDiagram D p₂).map m₂ ≫ u₂ :=
    pullback.lift_fst ..
  have hv₂snd : v₂ ≫ pullback.snd p₁ (D.map j₃.hom) = pullback.snd p₂ (D.map j₃.hom) :=
    pullback.lift_snd ..
  -- after base change to the limit they are the identifications with `X`
  have key₁ : (baseChangeCone D c p₁).π.app j₃ ≫ v₁ =
      H₁.isoPullback.inv ≫ H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv₁fst, ← Category.assoc, (baseChangeCone D c p₁).w m₁, hu₁a,
        Category.assoc, Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
    · rw [Category.assoc, hv₁snd, baseChangeCone_π_app_snd, Category.assoc, Category.assoc,
        baseChangeCone_π_app_snd, ← Category.assoc H₂.isoPullback.hom, hi₂snd,
        ← Category.assoc, hinvg₁]
  have key₂ : (baseChangeCone D c p₂).π.app j₃ ≫ v₂ =
      H₂.isoPullback.inv ≫ H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv₂fst, ← Category.assoc, (baseChangeCone D c p₂).w m₂, hu₂a,
        Category.assoc, Category.assoc, baseChangeCone_π_app_fst, hi₁fst]
    · rw [Category.assoc, hv₂snd, baseChangeCone_π_app_snd, Category.assoc, Category.assoc,
        baseChangeCone_π_app_snd, ← Category.assoc H₁.isoPullback.hom, hi₁snd,
        ← Category.assoc, hinvg₂]
  have hw₁ : (baseChangeCone D c p₁).π.app j₃ ≫ v₁ ≫ v₂ = (baseChangeCone D c p₁).π.app j₃ := by
    rw [← Category.assoc, key₁, Category.assoc, Category.assoc, key₂, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  have hw₂ : (baseChangeCone D c p₂).π.app j₃ ≫ v₂ ≫ v₁ = (baseChangeCone D c p₂).π.app j₃ := by
    rw [← Category.assoc, key₂, Category.assoc, Category.assoc, key₁, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  -- the two composites become the identity at a later stage
  obtain ⟨j₄, n₁, hn₁⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (baseChangeDiagram D p₁) (baseChangeDiagramStructure D p₁) p₁ (baseChangeCone D c p₁)
      (isLimitBaseChangeCone D c p₁ hc)
      (v₁ ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom)) (pullback.fst p₁ (D.map j₃.hom))
      (by
        change pullback.fst p₁ (D.map j₃.hom) ≫ p₁ = _
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₂, hv₂snd,
          ← Category.assoc, hv₁snd, ← pullback.condition])
      rfl
      (by
        have h := congrArg (· ≫ pullback.fst p₁ (D.map j₃.hom)) hw₁
        simp only [Category.assoc] at h ⊢
        exact h)
  obtain ⟨j₅, n₂, hn₂⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (baseChangeDiagram D p₂) (baseChangeDiagramStructure D p₂) p₂ (baseChangeCone D c p₂)
      (isLimitBaseChangeCone D c p₂ hc)
      (v₂ ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom)) (pullback.fst p₂ (D.map j₃.hom))
      (by
        change pullback.fst p₂ (D.map j₃.hom) ≫ p₂ = _
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₁, hv₁snd,
          ← Category.assoc, hv₂snd, ← pullback.condition])
      rfl
      (by
        have h := congrArg (· ≫ pullback.fst p₂ (D.map j₃.hom)) hw₂
        simp only [Category.assoc] at h ⊢
        exact h)
  obtain ⟨j₇, e, he⟩ := IsCofilteredOrEmpty.cone_maps
    (IsCofiltered.minToLeft j₄ j₅ ≫ n₁) (IsCofiltered.minToRight j₄ j₅ ≫ n₂)
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : j₇ ⟶ j₃, t = (e ≫ IsCofiltered.minToLeft j₄ j₅) ≫ n₁ ∧
      t = (e ≫ IsCofiltered.minToRight j₄ j₅) ≫ n₂ :=
    ⟨_, rfl, by rw [Category.assoc, he, Category.assoc]⟩
  have hcomp₁ : (baseChangeDiagram D p₁).map t ≫ v₁ ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom) =
      (baseChangeDiagram D p₁).map t ≫ pullback.fst p₁ (D.map j₃.hom) := by
    rw [ht₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [hn₁]
  have hcomp₂ : (baseChangeDiagram D p₂).map t ≫ v₂ ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom) =
      (baseChangeDiagram D p₂).map t ≫ pullback.fst p₂ (D.map j₃.hom) := by
    rw [ht₂]
    simp only [Functor.map_comp, Category.assoc]
    rw [hn₂]
  -- the isomorphism at the stage `j₇`
  set V₁ : (baseChangeDiagram D p₁).obj j₇ ⟶ (baseChangeDiagram D p₂).obj j₇ :=
    pullback.lift ((baseChangeDiagram D p₁).map t ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom))
      (pullback.snd p₁ (D.map j₇.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₁, hv₁snd,
            ← Category.assoc, baseChangeDiagram_map_snd, Category.assoc, ← D.map_comp,
            Over.w t]) with hV₁def
  set V₂ : (baseChangeDiagram D p₂).obj j₇ ⟶ (baseChangeDiagram D p₁).obj j₇ :=
    pullback.lift ((baseChangeDiagram D p₂).map t ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom))
      (pullback.snd p₂ (D.map j₇.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₂, hv₂snd,
            ← Category.assoc, baseChangeDiagram_map_snd, Category.assoc, ← D.map_comp,
            Over.w t]) with hV₂def
  have hV₁fst : V₁ ≫ pullback.fst p₂ (D.map j₇.hom) =
      (baseChangeDiagram D p₁).map t ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom) := pullback.lift_fst ..
  have hV₁snd : V₁ ≫ pullback.snd p₂ (D.map j₇.hom) = pullback.snd p₁ (D.map j₇.hom) :=
    pullback.lift_snd ..
  have hV₂fst : V₂ ≫ pullback.fst p₁ (D.map j₇.hom) =
      (baseChangeDiagram D p₂).map t ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom) := pullback.lift_fst ..
  have hV₂snd : V₂ ≫ pullback.snd p₁ (D.map j₇.hom) = pullback.snd p₂ (D.map j₇.hom) :=
    pullback.lift_snd ..
  have hnat₁ : V₁ ≫ (baseChangeDiagram D p₂).map t = (baseChangeDiagram D p₁).map t ≫ v₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeDiagram_map_fst, hV₁fst, Category.assoc]
    · rw [Category.assoc, baseChangeDiagram_map_snd, ← Category.assoc, hV₁snd,
        Category.assoc, hv₁snd, baseChangeDiagram_map_snd]
  have hnat₂ : V₂ ≫ (baseChangeDiagram D p₁).map t = (baseChangeDiagram D p₂).map t ≫ v₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeDiagram_map_fst, hV₂fst, Category.assoc]
    · rw [Category.assoc, baseChangeDiagram_map_snd, ← Category.assoc, hV₂snd,
        Category.assoc, hv₂snd, baseChangeDiagram_map_snd]
  have hVV₁ : V₁ ≫ V₂ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hV₂fst, ← Category.assoc, hnat₁]
      simp only [Category.assoc]
      rw [hcomp₁, baseChangeDiagram_map_fst, Category.id_comp]
    · rw [Category.assoc, hV₂snd, hV₁snd, Category.id_comp]
  have hVV₂ : V₂ ≫ V₁ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hV₁fst, ← Category.assoc, hnat₂]
      simp only [Category.assoc]
      rw [hcomp₂, baseChangeDiagram_map_fst, Category.id_comp]
    · rw [Category.assoc, hV₁snd, hV₂snd, Category.id_comp]
  have key₁' : (baseChangeCone D c p₁).π.app j₃ ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom) =
      H₁.isoPullback.inv ≫ h₂ := by
    rw [← Category.assoc, key₁, Category.assoc, Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
  have hcompat : (H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₇) ≫ V₁ =
      H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₇ := by
    apply pullback.hom_ext
    · have hlhs : ((H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₇) ≫ V₁) ≫
          pullback.fst p₂ (D.map j₇.hom) = h₂ := by
        simp only [Category.assoc, hV₁fst]
        rw [← Category.assoc ((baseChangeCone D c p₁).π.app j₇), (baseChangeCone D c p₁).w t,
          key₁', Iso.hom_inv_id_assoc]
      have hrhs : (H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₇) ≫
          pullback.fst p₂ (D.map j₇.hom) = h₂ := by
        rw [Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
      rw [hlhs, hrhs]
    · rw [Category.assoc, Category.assoc, hV₁snd, baseChangeCone_π_app_snd, ← Category.assoc,
        hi₁snd, Category.assoc, baseChangeCone_π_app_snd, ← Category.assoc, hi₂snd]
  -- transport to arbitrary models of the base changes
  refine ⟨j₇.left, j₇.hom, ?_⟩
  intro Y₁' Y₂' p₁' q₁ p₂' q₂ h₁' h₂' HH₁ hh₁ hh₁' HH₂ hh₂ hh₂'
  have hα₁fst : HH₁.isoPullback.hom ≫ pullback.fst p₁ (D.map j₇.hom) = q₁ :=
    IsPullback.isoPullback_hom_fst _
  have hα₁snd : HH₁.isoPullback.hom ≫ pullback.snd p₁ (D.map j₇.hom) = p₁' :=
    IsPullback.isoPullback_hom_snd _
  have hα₂fst : HH₂.isoPullback.hom ≫ pullback.fst p₂ (D.map j₇.hom) = q₂ :=
    IsPullback.isoPullback_hom_fst _
  have hα₂snd : HH₂.isoPullback.hom ≫ pullback.snd p₂ (D.map j₇.hom) = p₂' :=
    IsPullback.isoPullback_hom_snd _
  have hh₁α : h₁' ≫ HH₁.isoPullback.hom =
      H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₇ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₁fst, hh₁, Category.assoc, baseChangeCone_π_app_fst, hi₁fst]
    · rw [Category.assoc, hα₁snd, hh₁', Category.assoc, baseChangeCone_π_app_snd,
        ← Category.assoc, hi₁snd]
  have hh₂α : h₂' ≫ HH₂.isoPullback.hom =
      H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₇ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₂fst, hh₂, Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
    · rw [Category.assoc, hα₂snd, hh₂', Category.assoc, baseChangeCone_π_app_snd,
        ← Category.assoc, hi₂snd]
  refine ⟨HH₁.isoPullback ≪≫ ⟨V₁, V₂, hVV₁, hVV₂⟩ ≪≫ HH₂.isoPullback.symm, ?_, ?_⟩
  · change HH₁.isoPullback.hom ≫ V₁ ≫ HH₂.isoPullback.inv ≫ p₂' = p₁'
    rw [show HH₂.isoPullback.inv ≫ p₂' = pullback.snd p₂ (D.map j₇.hom) by
      rw [Iso.inv_comp_eq, hα₂snd], hV₁snd, hα₁snd]
  · change h₁' ≫ HH₁.isoPullback.hom ≫ V₁ ≫ HH₂.isoPullback.inv = h₂'
    rw [← Category.assoc, ← Category.assoc, hh₁α, hcompat, ← hh₂α, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

end Descent

end FinitePresentationDescent

end AlgebraicGeometry
