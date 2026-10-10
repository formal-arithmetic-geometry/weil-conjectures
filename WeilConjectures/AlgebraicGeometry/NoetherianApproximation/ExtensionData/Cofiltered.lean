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
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.ExistsStage
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
# The category of stages is cofiltered

The category of stages of an induction step of absolute Noetherian approximation is cofiltered,
and the functor `ExtensionData.stageIndex` remembering the underlying index is initial.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
namespace Scheme.NoetherianApproximation
namespace ExtensionData

variable (E : ExtensionData.{u})

/-- (Implementation) A finite-conjunction helper: a family of index-stable properties, each
attainable below any index, is attained jointly below any index. -/
private lemma exists_hom_forall {j₂ : Over E.i₀}
    (P : ∀ (j' : Over E.i₀), (j' ⟶ j₂) → Fin E.n → Prop)
    (hstab : ∀ {j j' : Over E.i₀} (k' : j' ⟶ j) (k : j ⟶ j₂) (l : Fin E.n),
      P j k l → P j' (k' ≫ k) l)
    (hex : ∀ (j : Over E.i₀) (k : j ⟶ j₂) (l : Fin E.n),
      ∃ (j' : Over E.i₀) (k' : j' ⟶ j), P j' (k' ≫ k) l) :
    ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l, P j k l := by
  classical
  suffices h : ∀ s : Finset (Fin E.n), ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l ∈ s, P j k l by
    obtain ⟨j, k, hj⟩ := h Finset.univ
    exact ⟨j, k, fun l ↦ hj l (Finset.mem_univ l)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨j₂, 𝟙 j₂, by simp⟩
  | insert a s ha ih =>
    obtain ⟨j, k, hj⟩ := ih
    obtain ⟨j', k', hj'⟩ := hex j k a
    refine ⟨j', k' ≫ k, fun l hl ↦ ?_⟩
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hj'
    · exact hstab k' k l (hj l hl)

/-- (Implementation) The lifts of the generators of the intersection exist at a common
index below any given index. -/
lemma exists_r (j₀ : Over E.i₀) :
    ∃ (j : Over E.i₀) (_ : j ⟶ j₀) (r : Fin E.n → Γ(E.WD.obj j, ⊤)),
      ∀ l, E.t j (r l) = E.sV (E.b l) := by
  have hex : ∀ (j : Over E.i₀) (l : Fin E.n),
      ∃ (j' : Over E.i₀) (_ : j' ⟶ j) (r : Γ(E.WD.obj j', ⊤)), E.t j' r = E.sV (E.b l) := by
    intro j l
    obtain ⟨i, r₀, hr₀⟩ := exists_appTop_π_eq_of_isLimit E.WD E.Wc E.isLimitWc (E.sV (E.b l))
    obtain ⟨j', kj, ki, -⟩ := IsCofilteredOrEmpty.cone_objs j i
    exact ⟨j', kj, E.res ki r₀, by rw [E.t_res]; exact hr₀.symm⟩
  obtain ⟨j, k, h⟩ := E.exists_hom_forall (j₂ := j₀)
    (fun j' _ l ↦ ∃ r, E.t j' r = E.sV (E.b l))
    (fun {j j'} k' k l hl ↦ by
      obtain ⟨r, hr⟩ := hl
      exact ⟨E.res k' r, by rw [E.t_res]; exact hr⟩)
    (fun j k l ↦ by
      obtain ⟨j', k', r, hr⟩ := hex j l
      exact ⟨j', k', r, hr⟩)
  choose r hr using h
  exact ⟨j, k, r, hr⟩

/-- (Implementation) The basic opens of the limit lifts of the generators are affine: they
are the basic opens of the affine `V`, transported into the limit `W`. -/
lemma isAffineOpen_basicOpen_sV (l : Fin E.n) :
    IsAffineOpen (E.Wc.pt.basicOpen (E.sV (E.b l))) := by
  rw [E.basicOpen_sV]
  exact (E.hV.basicOpen (E.b l)).preimage_of_isOpenImmersion _
    (by rw [E.opensRange_WUι_comp_Uι]; exact E.hb l)

/-- (Implementation) Below any index, there is a pre-stage: lifts of the generators whose
basic opens are affine and cover. The covering condition descends from the limit by
`exists_map_eq_top`, and affineness by descending the affine limit basic open
(Stacks 01Z4). -/
lemma exists_preStage_hom (j₀ : Over E.i₀) :
    ∃ (P : E.PreStage), Nonempty (P.j ⟶ j₀) := by
  -- Step 1: lifts with the covering condition.
  obtain ⟨j₁, k₁, r, hr⟩ := E.exists_r j₀
  have hU : E.Wc.π.app j₁ ⁻¹ᵁ (⨆ l, (E.WD.obj j₁).basicOpen (r l)) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup]
    simp_rw [Scheme.preimage_basicOpen_top]
    have h : ∀ l, (E.Wc.π.app j₁).appTop (r l) = E.sV (E.b l) := hr
    simp_rw [h]
    exact E.iSup_basicOpen_sV
  obtain ⟨j₂, k₂, hk₂⟩ := exists_map_eq_top E.WD E.Wc E.isLimitWc _ hU
  set r₂ : Fin E.n → Γ(E.WD.obj j₂, ⊤) := fun l ↦ E.res k₂ (r l) with hr₂def
  have hr₂ : ∀ l, E.t j₂ (r₂ l) = E.sV (E.b l) := fun l ↦ by rw [hr₂def, E.t_res, hr]
  have hcov₂ : ⨆ l, (E.WD.obj j₂).basicOpen (r₂ l) = ⊤ := by
    have hb : ∀ l, (E.WD.obj j₂).basicOpen (r₂ l) =
        E.WD.map k₂ ⁻¹ᵁ ((E.WD.obj j₁).basicOpen (r l)) :=
      fun l ↦ (Scheme.preimage_basicOpen_top (E.WD.map k₂) (r l)).symm
    simp_rw [hb, ← Scheme.Hom.preimage_iSup, hk₂]
  -- Step 2: affineness of the basic opens, by descending the affine limit basic open
  -- and equalizing (Stacks 01Z4).
  have hex : ∀ (j : Over E.i₀) (k : j ⟶ j₂) (l : Fin E.n),
      ∃ (ja : Over E.i₀) (ka : ja ⟶ j),
        IsAffineOpen ((E.WD.obj ja).basicOpen (E.res (ka ≫ k) (r₂ l))) := by
    intro j k l
    obtain ⟨i, O, hO, hOeq⟩ := exists_isAffineOpen_preimage_eq E.WD E.Wc E.isLimitWc _
      (E.isAffineOpen_basicOpen_sV l)
    obtain ⟨j', kj, ki, -⟩ := IsCofilteredOrEmpty.cone_objs j i
    have hpre : E.Wc.π.app j' ⁻¹ᵁ ((E.WD.obj j').basicOpen (E.res (kj ≫ k) (r₂ l))) =
        E.Wc.π.app j' ⁻¹ᵁ (E.WD.map ki ⁻¹ᵁ O) := by
      rw [Scheme.preimage_basicOpen_top, ← Scheme.Hom.comp_preimage, E.Wc.w ki, hOeq]
      congr 1
      exact (E.t_res (kj ≫ k) (r₂ l)).trans (hr₂ l)
    obtain ⟨j'', k'', heq⟩ := exists_map_preimage_eq_map_preimage E.WD E.Wc E.isLimitWc
      (TopologicalSpace.NoetherianSpace.isCompact _)
      (TopologicalSpace.NoetherianSpace.isCompact _) hpre
    refine ⟨j'', k'' ≫ kj, ?_⟩
    have e : (E.WD.obj j'').basicOpen (E.res ((k'' ≫ kj) ≫ k) (r₂ l)) =
        E.WD.map k'' ⁻¹ᵁ ((E.WD.obj j').basicOpen (E.res (kj ≫ k) (r₂ l))) := by
      rw [Scheme.preimage_basicOpen_top]
      congr 1
      rw [Category.assoc]
      exact (E.res_res (kj ≫ k) k'' _).symm
    rw [e, heq]
    exact (hO.preimage (E.WD.map ki)).preimage (E.WD.map k'')
  obtain ⟨j₃, k₃, h₃⟩ := E.exists_hom_forall (j₂ := j₂)
    (fun j' k l ↦ IsAffineOpen ((E.WD.obj j').basicOpen (E.res k (r₂ l))))
    (fun {j j'} k' k l hl ↦ by
      have e : (E.WD.obj j').basicOpen (E.res (k' ≫ k) (r₂ l)) =
          E.WD.map k' ⁻¹ᵁ ((E.WD.obj j).basicOpen (E.res k (r₂ l))) := by
        rw [Scheme.preimage_basicOpen_top]
        congr 1
        exact (E.res_res k k' _).symm
      rw [e]
      exact hl.preimage _)
    hex
  have hcov₃ : ⨆ l, (E.WD.obj j₃).basicOpen (E.res k₃ (r₂ l)) = ⊤ := by
    have hb : ∀ l, (E.WD.obj j₃).basicOpen (E.res k₃ (r₂ l)) =
        E.WD.map k₃ ⁻¹ᵁ ((E.WD.obj j₂).basicOpen (r₂ l)) :=
      fun l ↦ (Scheme.preimage_basicOpen_top (E.WD.map k₃) (r₂ l)).symm
    simp_rw [hb, ← Scheme.Hom.preimage_iSup, hcov₂, Scheme.Hom.preimage_top]
  exact ⟨⟨j₃, fun l ↦ E.res k₃ (r₂ l), fun l ↦ by rw [E.t_res, hr₂], hcov₃, h₃⟩,
    ⟨(k₃ ≫ k₂) ≫ k₁⟩⟩

/-- (Implementation) Equalize two families of sections with equal limit restrictions at a
common finer index. -/
lemma exists_hom_res_eq {j₂ : Over E.i₀} (x y : Fin E.n → Γ(E.WD.obj j₂, ⊤))
    (h : ∀ l, E.t j₂ (x l) = E.t j₂ (y l)) :
    ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l, E.res k (x l) = E.res k (y l) := by
  apply E.exists_hom_forall (fun j k l ↦ E.res k (x l) = E.res k (y l))
  · intro j j' k' k l hl
    exact (E.res_res k k' _).symm.trans
      ((congrArg (fun z ↦ E.res k' z) hl).trans (E.res_res k k' _))
  · intro j k l
    have hcpt : IsCompact ((⊤ : (E.WD.obj j).Opens) : Set (E.WD.obj j)) := isCompact_univ
    obtain ⟨j', k', hk'⟩ := exists_app_map_eq_map_of_isLimit E.WD E.Wc E.isLimitWc hcpt
      (E.res k (x l)) (E.res k (y l))
      (show E.t j (E.res k (x l)) = E.t j (E.res k (y l)) by rw [E.t_res, E.t_res, h])
    refine ⟨j', k', ?_⟩
    exact (E.res_res k k' _).symm.trans (hk'.trans (E.res_res k k' _))

instance : Nonempty E.Stage := by
  obtain ⟨P, -⟩ := E.exists_preStage_hom (Over.mk (𝟙 E.i₀))
  exact ⟨P.stage⟩

instance : IsCofilteredOrEmpty E.Stage where
  cone_objs T₁ T₂ := by
    obtain ⟨j', k₁, k₂, -⟩ := IsCofilteredOrEmpty.cone_objs T₁.j T₂.j
    obtain ⟨j, k, hk⟩ := E.exists_hom_res_eq (fun l ↦ E.res k₁ (T₁.r l))
      (fun l ↦ E.res k₂ (T₂.r l)) (fun l ↦ by rw [E.t_res, E.t_res, T₁.hr, T₂.hr])
    have hmap : T₂.A.map (resAlgHom (k ≫ k₂)) ≤ E.fiberProduct j := by
      rintro p ⟨q, hq, rfl⟩
      exact resAlgHom_mem_fiberProduct _ (T₂.A_le_fiberProduct hq)
    -- Stated for a general subalgebra `A'`: for the concrete one, elaborating the components
    -- of the morphism to `T₂` is very slow.
    have H (A' : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤))) (hA' : A' ≤ E.fiberProduct j)
        (hfg : A'.FG) (hle : T₂.A.map (resAlgHom (k ≫ k₂)) ≤ A') :
        ∃ (W : E.Stage) (_ : W ⟶ T₁) (_ : W ⟶ T₂), True :=
      ⟨T₁.restrict (k ≫ k₁) A' hA' hfg, T₁.restrictHom _ _ _ _,
        ⟨k ≫ k₂, fun l ↦ (E.res_res k₂ k _).symm.trans ((hk l).symm.trans (E.res_res k₁ k _)),
          fun p hp ↦ T₁.le_restrict_A _ _ _ _ (hle ⟨p, hp, rfl⟩)⟩, trivial⟩
    exact H _ hmap (T₂.hAfg.map _) le_rfl
  cone_maps T₁ T₂ f g := by
    obtain ⟨j', k, hk⟩ := IsCofilteredOrEmpty.cone_maps f.base g.base
    refine ⟨T₁.restrict k ⊥ bot_le Subalgebra.fg_bot, T₁.restrictHom _ _ _ _, ?_⟩
    exact E.stageHom_ext (by simpa using hk)

instance : IsCofiltered E.Stage where

/-- (Implementation) The index functor from stages to the base indices. By
`exists_preStage_hom` and the restriction construction it is initial: limits over the
system of the `Wⱼ` may be computed over the category of stages. -/
@[simps] def stageIndex : E.Stage ⥤ Over E.i₀ where
  obj T := T.j
  map f := f.base

instance : E.stageIndex.Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro j
    obtain ⟨P, ⟨k⟩⟩ := E.exists_preStage_hom j
    exact ⟨P.stage, ⟨k⟩⟩
  · intro j T s s'
    obtain ⟨j', k, hk⟩ := IsCofilteredOrEmpty.cone_maps s s'
    exact ⟨T.restrict k ⊥ bot_le Subalgebra.fg_bot, T.restrictHom _ _ _ _, by simpa using hk⟩

end ExtensionData

end Scheme.NoetherianApproximation

end AlgebraicGeometry
