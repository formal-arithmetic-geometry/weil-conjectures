/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Checking the limit property of a cofiltered limit of schemes locally on a stage

Mathlib's `AlgebraicGeometry.isLimitOpensCone` says that a limit cone over a cofiltered
diagram `{Dᵢ}` of schemes restricts, over any open `V ⊆ Dᵢ`, to a limit cone over the
diagram of the preimages of `V`. Here we prove the converse: a cone `c` over `{Dᵢ}` is a
limit cone as soon as its restrictions to the members of an open cover of one stage, and
to their pairwise intersections, are limit cones. No assumption on the transition
morphisms is needed.

## Main results

* `AlgebraicGeometry.isLimitOfIsLimitOpensCone`: being a limit cone over a cofiltered
  diagram of schemes is local on a stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The open cover of the point of a cone `s` over `D` by the preimages of a covering
family of opens of the stage `D.obj i₀`. -/
noncomputable def preimageOpenCover (i₀ : I) {σ : Type*} (U : σ → (D.obj i₀).Opens)
    (hU : ⨆ a, U a = ⊤) (s : Cone D) : s.pt.OpenCover :=
  Scheme.Cover.mkOfCovers σ (fun a ↦ (s.π.app i₀ ⁻¹ᵁ U a).toScheme)
    (fun a ↦ Scheme.Opens.ι _)
    (fun x ↦ by
      have : s.π.app i₀ x ∈ ⨆ a, U a := by
        rw [hU]
        trivial
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact ⟨a, ⟨x, ha⟩, rfl⟩)

variable {c} in
/-- The universal morphism to the restriction of `c` to an open `V` of the stage
`D.obj i₀`, composed back into the tower of the cone `c`, agrees with the cone `s`. -/
lemma lift_opensCone_ι_comp {i₀ : I} {V : (D.obj i₀).Opens}
    (hV : IsLimit (opensCone D c i₀ V)) (s : Cone D) (j : Over i₀) :
    hV.lift (opensCone D s i₀ V) ≫ (c.π.app i₀ ⁻¹ᵁ V).ι ≫ c.π.app j.left =
      (s.π.app i₀ ⁻¹ᵁ V).ι ≫ s.π.app j.left := by
  have h1 := congrArg (· ≫ (D.map j.hom ⁻¹ᵁ V).ι) (hV.fac (opensCone D s i₀ V) j)
  simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι] at h1
  simpa using h1

variable {c} in
/-- Compatibility on overlaps of the local universal morphisms into the restrictions of
`c`, as needed to glue them over `AlgebraicGeometry.preimageOpenCover`. -/
lemma lift_opensCone_ι_compat {i₀ : I} {σ : Type*} {U : σ → (D.obj i₀).Opens}
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a)))
    (h₂ : ∀ a b, a ≠ b → IsLimit (opensCone D c i₀ (U a ⊓ U b))) (s : Cone D) (a b : σ) :
    pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) =
      pullback.snd _ _ ≫ ((h b).lift (opensCone D s i₀ (U b)) ≫ (c.π.app i₀ ⁻¹ᵁ U b).ι) := by
  have hq' : pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
      (s.π.app i₀ ⁻¹ᵁ U a).ι = pullback.snd _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U b).ι :=
    pullback.condition
  have hqmem (t : ↑(pullback ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι))) :
      s.π.app i₀ ((pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        (s.π.app i₀ ⁻¹ᵁ U a).ι) t) ∈ U a ⊓ U b := by
    constructor
    · rw [Scheme.Hom.comp_apply]
      exact (pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) t).2
    · rw [hq', Scheme.Hom.comp_apply]
      exact (pullback.snd ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) t).2
  have h0 (x : σ) : (h x).lift (opensCone D s i₀ (U x)) ≫
      (c.π.app i₀ ⁻¹ᵁ U x).ι ≫ c.π.app i₀ = (s.π.app i₀ ⁻¹ᵁ U x).ι ≫ s.π.app i₀ :=
    lift_opensCone_ι_comp D (h x) s (Over.mk (𝟙 i₀))
  have key (e : pullback ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ⟶ c.pt)
      (he : e ≫ c.π.app i₀ = (pullback.fst _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U a).ι) ≫ s.π.app i₀) :
      Set.range e ⊆ Set.range ((c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι) := by
    rintro - ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (e ≫ c.π.app i₀) t ∈ U a ⊓ U b
    rw [he]
    exact hqmem t
  have he_a : (pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
      ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι)) ≫ c.π.app i₀ =
      (pullback.fst _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U a).ι) ≫ s.π.app i₀ := by
    simp only [Category.assoc]
    rw [h0 a]
  have he_b : (pullback.snd ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
      ((h b).lift (opensCone D s i₀ (U b)) ≫ (c.π.app i₀ ⁻¹ᵁ U b).ι)) ≫ c.π.app i₀ =
      (pullback.fst _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U a).ι) ≫ s.π.app i₀ := by
    simp only [Category.assoc]
    rw [h0 b, reassoc_of% hq']
  -- both sides factor through the overlap `c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)`
  have hfac_a := (IsOpenImmersion.lift_fac ((c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι) _ (key _ he_a)).symm
  have hfac_b := (IsOpenImmersion.lift_fac ((c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι) _ (key _ he_b)).symm
  rw [hfac_a, hfac_b]
  congr 1
  have hab : IsLimit (opensCone D c i₀ (U a ⊓ U b)) := by
    classical
    by_cases hne : a = b
    · subst hne
      rw [inf_idem]
      exact h a
    · exact h₂ a b hne
  apply hab.hom_ext
  intro j
  rw [← cancel_mono (D.map j.hom ⁻¹ᵁ (U a ⊓ U b)).ι]
  simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc]
  simp only [Category.assoc]
  rw [lift_opensCone_ι_comp D (h a) s j, lift_opensCone_ι_comp D (h b) s j,
    reassoc_of% hq']

/-- **Being a limit cone is local on a stage.** Let `{Dᵢ}` be a cofiltered diagram of
schemes and let `c` be a cone over it. Suppose some stage `D.obj i₀` has an open cover
`{U a}` such that the restriction of `c` to every `U a`, and to every intersection
`U a ⊓ U b` with `a ≠ b`, is a limit cone. Then `c` is a limit cone.

This is a converse to `AlgebraicGeometry.isLimitOpensCone`. -/
noncomputable def isLimitOfIsLimitOpensCone [IsCofiltered I] (i₀ : I) {σ : Type*}
    (U : σ → (D.obj i₀).Opens) (hU : ⨆ a, U a = ⊤)
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a)))
    (h₂ : ∀ a b, a ≠ b → IsLimit (opensCone D c i₀ (U a ⊓ U b))) : IsLimit c where
  lift s := (preimageOpenCover D i₀ U hU s).glueMorphisms
    (fun a ↦ (h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι)
    (lift_opensCone_ι_compat D h h₂ s)
  fac s j := by
    obtain ⟨k, fkj, fki₀, -⟩ := IsCofilteredOrEmpty.cone_objs j i₀
    rw [← c.w fkj, ← s.w fkj, ← Category.assoc]
    congr 1
    apply (preimageOpenCover D i₀ U hU s).hom_ext
    intro a
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
    change ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) ≫ c.π.app k =
      (s.π.app i₀ ⁻¹ᵁ U a).ι ≫ s.π.app k
    rw [Category.assoc]
    exact lift_opensCone_ι_comp D (h a) s (Over.mk fki₀)
  uniq s m hm := by
    apply (preimageOpenCover D i₀ U hU s).hom_ext
    intro a
    rw [Scheme.Cover.ι_glueMorphisms]
    change (s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m =
      (h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι
    have hrange : Set.range ((s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m) ⊆
        Set.range ((c.π.app i₀ ⁻¹ᵁ U a).ι) := by
      rintro - ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (((s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m) ≫ c.π.app i₀) t ∈ U a
      rw [Category.assoc, hm i₀]
      exact t.2
    have hma : IsOpenImmersion.lift ((c.π.app i₀ ⁻¹ᵁ U a).ι)
        ((s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m) hrange = (h a).lift (opensCone D s i₀ (U a)) := by
      apply (h a).hom_ext
      intro j
      rw [← cancel_mono (D.map j.hom ⁻¹ᵁ U a).ι]
      simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι]
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hm j.left]
      exact (lift_opensCone_ι_comp D (h a) s j).symm
    rw [← hma, IsOpenImmersion.lift_fac]

@[reassoc]
lemma opensDiagram_map_ι (i : I) (U : (D.obj i).Opens) {j j' : Over i} (k : j ⟶ j') :
    (opensDiagram D i U).map k ≫ Scheme.Opens.ι (D.map j'.hom ⁻¹ᵁ U) =
      Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ U) ≫ D.map k.left :=
  (opensDiagramι D i U).naturality k

@[reassoc]
lemma opensCone_π_ι (c : Cone D) (i : I) (U : (D.obj i).Opens) (j : Over i) :
    (opensCone D c i U).π.app j ≫ Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ U) =
      Scheme.Opens.ι (c.π.app i ⁻¹ᵁ U) ≫ c.π.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

end AlgebraicGeometry
