/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.Chart
public import WeilConjectures.Mathlib.RingTheory.Etale.FiniteSplitting

/-!
# Existence of split neighbourhoods

Let `f : X ⟶ Y` be finite and `y : Spec Ω ⟶ Y` a geometric point with `Ω` algebraically
closed. We show that every pointed étale neighbourhood `(U, u)` of `y` is refined by a split
neighbourhood (`AlgebraicGeometry.Scheme.Hom.SplitNeighborhood.exists_hom`): choosing an affine
chart `Spec R' ⊆ U`, the ring-theoretic splitting result
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_tensor_eq` provides an étale
`R'`-algebra `A'` with a point over `u` and a complete system of orthogonal idempotents of
`A' ⊗ Γ(X, f ⁻¹ᵁ Y₀)`, indexed by the geometric points of `X` over `y`, and the basic opens of
these idempotents are the pieces of the decomposition of `Spec A' ×_Y X`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct RingHom

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] affineAlgebra Chart.algebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

namespace Chart

variable {Y₀ : Y.Opens} (hY₀ : IsAffineOpen Y₀) (hy : y default ∈ Y₀) {c : EtaleNeighborhood y}
  (ch : Chart y Y₀ c) (A' : Type u) [CommRing A'] [Algebra ch.ring A'] [Algebra.Etale ch.ring A']
  (φ' : A' →+* Ω) (hφ' : φ'.comp (algebraMap ch.ring A') = ch.point)
  [Fintype (PointsOver ch.point (ch.Fiber f))] [DecidableEq (PointsOver ch.point (ch.Fiber f))]
  (e : PointsOver ch.point (ch.Fiber f) → ch.RefineFiber f A')
  (he : CompleteOrthogonalIdempotents e)
  (hval : ∀ t t' : PointsOver ch.point (ch.Fiber f),
    t'.tensor hφ' (e t) = if t' = t then 1 else 0)

/-- The split neighbourhood `Spec A'` of `y` given by a complete system of orthogonal
idempotents `e` of the ring of `Spec A' ×_Y X`, indexed by the points of the fibre, with
`e t` supported exactly at the point `t`: the pieces are the basic opens of the `e t`. -/
def split : SplitNeighborhood f y where
  obj := ch.refine hY₀ A' φ' hφ'
  piece t := (ch.refineIso f hY₀ A' φ' hφ').inv ⁻¹ᵁ
    (PrimeSpectrum.basicOpen (e (ch.fiberBasePoint f hY₀ hy t)))
  disjoint t t' h := by
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, ← PrimeSpectrum.basicOpen_mul,
      he.ortho ((ch.bijective_fiberBasePoint f hY₀ hy).1.ne h), PrimeSpectrum.basicOpen_zero,
      Scheme.Hom.preimage_bot]
  iSup_eq := by
    rw [← Scheme.Hom.preimage_iSup, PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr,
      Scheme.Hom.preimage_top]
    rw [Ideal.eq_top_iff_one, ← he.complete]
    refine Ideal.sum_mem _ fun s _ ↦ Ideal.subset_span ?_
    obtain ⟨t, rfl⟩ := (ch.bijective_fiberBasePoint f hY₀ hy).2 s
    exact ⟨t, rfl⟩
  mem t := by
    change (ch.refineIso f hY₀ A' φ' hφ').inv (basePt f _ t default) ∈
      PrimeSpectrum.basicOpen (e (ch.fiberBasePoint f hY₀ hy t))
    rw [ch.basePt_refine f hY₀ hy A' φ' hφ' t, Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply (ch.refineIso f hY₀ A' φ' hφ').hom, Iso.hom_inv_id]
    change Spec.map (CommRingCat.ofHom (ch.fiberPoint f hY₀ hy A' φ' hφ' t).1)
      (default : Spec (.of Ω)) ∈ _
    rw [Spec.map_default_mem_basicOpen_iff]
    change (ch.fiberBasePoint f hY₀ hy t).tensor hφ' (e (ch.fiberBasePoint f hY₀ hy t)) ≠ 0
    rw [hval, if_pos rfl]
    exact one_ne_zero

@[simp]
lemma split_obj : (ch.split f hY₀ hy A' φ' hφ' e he hval).obj = ch.refine hY₀ A' φ' hφ' := rfl

@[simp]
lemma split_piece (t : GeometricFiber f y) :
    (ch.split f hY₀ hy A' φ' hφ' e he hval).piece t = (ch.refineIso f hY₀ A' φ' hφ').inv ⁻¹ᵁ
      (PrimeSpectrum.basicOpen (e (ch.fiberBasePoint f hY₀ hy t))) := rfl

end Chart

namespace SplitNeighborhood

variable (y)

/-- **Existence of split neighbourhoods**: every pointed étale neighbourhood of `y` is refined
by a split neighbourhood. -/
theorem exists_hom (c : EtaleNeighborhood y) :
    ∃ s : SplitNeighborhood f y, Nonempty (s.obj ⟶ c) := by
  classical
  obtain ⟨Y₀, hY₀, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y default) (U := ⊤) trivial
  obtain ⟨ch⟩ := Chart.nonempty y hy c
  have := ch.finite_fiber f hY₀
  have := Fintype.ofFinite (PointsOver ch.point (ch.Fiber f))
  obtain ⟨A', _, _, _, φ', hφ', e, he, hval⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_tensor_eq (A := ch.ring)
      (B := ch.Fiber f) ch.point
  exact ⟨ch.split f hY₀ hy A' φ' hφ' e he hval, ⟨ch.refineMap hY₀ A' φ' hφ'⟩⟩

variable {f y}

/-- **Pairwise disjoint pieces containing the points `(u, t)` cover after shrinking**: given
such pieces of `U ×_Y X`, there is a refinement `(U', u') ⟶ (U, u)` on which their preimages
form a split neighbourhood. -/
lemma exists_hom_piece_eq (c : EtaleNeighborhood y)
    (P : GeometricFiber f y → (pullback c.1.hom f).Opens)
    (hdisj : ∀ t t', t ≠ t' → Disjoint (P t) (P t'))
    (hmem : ∀ t, basePt f c t default ∈ P t) :
    ∃ (s : SplitNeighborhood f y) (g : s.obj ⟶ c),
      ∀ t, s.piece t = (f.Etale.map g.val).left ⁻¹ᵁ P t := by
  let C : Set (pullback c.1.hom f : Scheme.{u}) := (↑(⨆ t, P t))ᶜ
  have hC : IsClosed C := (⨆ t, P t).isOpen.isClosed_compl
  obtain ⟨c', g, hg⟩ := exists_hom_preimage_eq_bot f c C hC
    (fun t h ↦ h (TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hmem t⟩))
  refine ⟨⟨c', fun t ↦ (f.Etale.map g.val).left ⁻¹ᵁ P t, fun t t' h ↦ ?_, ?_, fun t ↦ ?_⟩,
    g, fun t ↦ rfl⟩
  · rw [disjoint_iff, ← Scheme.Hom.preimage_inf, (hdisj t t' h).eq_bot, Scheme.Hom.preimage_bot]
  · rw [← Scheme.Hom.preimage_iSup]
    ext w
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    by_contra hw
    have hwC : w ∈ (f.Etale.map g.val).left.base ⁻¹' C := hw
    rwa [hg] at hwC
  · have := hmem t
    rwa [← basePt_comp_etale_map_left f g t, Scheme.Hom.comp_apply] at this

/-- The category of split neighbourhoods is cofiltered. -/
instance isCofiltered : IsCofiltered (SplitNeighborhood f y) where
  nonempty := by
    obtain ⟨s, -⟩ := exists_hom f y (IsCofiltered.nonempty (C := EtaleNeighborhood y)).some
    exact ⟨s⟩
  cone_objs s₁ s₂ := by
    obtain ⟨c, g₁, g₂, -⟩ := IsCofilteredOrEmpty.cone_objs s₁.obj s₂.obj
    obtain ⟨s, g, hg⟩ := exists_hom_piece_eq c
      (fun t ↦ (f.Etale.map g₁.val).left ⁻¹ᵁ s₁.piece t ⊓ (f.Etale.map g₂.val).left ⁻¹ᵁ s₂.piece t)
      (fun t t' h ↦ by
        rw [disjoint_iff, inf_inf_inf_comm, ← Scheme.Hom.preimage_inf, (s₁.disjoint t t' h).eq_bot,
          Scheme.Hom.preimage_bot, bot_inf_eq])
      (fun t ↦ ⟨by
        have := s₁.mem t
        rwa [← basePt_comp_etale_map_left f g₁ t, Scheme.Hom.comp_apply] at this, by
        have := s₂.mem t
        rwa [← basePt_comp_etale_map_left f g₂ t, Scheme.Hom.comp_apply] at this⟩)
    refine ⟨s, ⟨g ≫ g₁, fun t ↦ ?_⟩, ⟨g ≫ g₂, fun t ↦ ?_⟩, trivial⟩
    · rw [hg, CategoryOfElements.comp_val, Hom.etale_map_left_comp_preimage]
      exact Scheme.Hom.preimage_mono _ inf_le_left
    · rw [hg, CategoryOfElements.comp_val, Hom.etale_map_left_comp_preimage]
      exact Scheme.Hom.preimage_mono _ inf_le_right
  cone_maps s₁ s₂ g h := by
    obtain ⟨c, k, hk⟩ := IsCofilteredOrEmpty.cone_maps g.val h.val
    exact ⟨s₁.pullbackDec k, s₁.pullbackDecHom k, hom_ext (by rwa [comp_val, comp_val])⟩

/-- **The forgetful functor from split neighbourhoods to pointed étale neighbourhoods is
initial**: the split neighbourhoods are cofinal among all pointed étale neighbourhoods. -/
instance initial_forget : (forget f y).Initial :=
  Functor.initial_of_exists_of_isCofiltered _ (fun c ↦ exists_hom f y c) fun {c s} g h ↦ by
    obtain ⟨c', k, hk⟩ := IsCofilteredOrEmpty.cone_maps g h
    exact ⟨s.pullbackDec k, s.pullbackDecHom k, hk⟩

end SplitNeighborhood

end AlgebraicGeometry.Scheme.Hom

end
