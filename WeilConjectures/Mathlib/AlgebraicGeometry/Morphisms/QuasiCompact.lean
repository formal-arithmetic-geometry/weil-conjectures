/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Points in the closure of the range of a quasi-compact morphism

A point in the closure of the range of a quasi-compact morphism to an affine scheme is
a specialization of a point of the range
(`AlgebraicGeometry.exists_specializes_of_mem_closure_range`). This is the topological
core of Stacks Project Tag 02JQ.

We also record retrocompactness, `AlgebraicGeometry.Scheme.Opens.quasiCompact_ι`: the
inclusion of a quasi-compact open of a quasi-separated scheme is a quasi-compact
morphism.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **A point in the closure of the range of a quasi-compact morphism to an affine
scheme is a specialization of a point of the range** (the topological core of Stacks
Project Tag 02JQ): the point corresponds to a prime containing the kernel of one of
finitely many affine chart maps; a prime of the chart ring contracting into it exists
by Stacks Tag 00FK (`Ideal.exists_ideal_comap_le_prime`), and the corresponding point
of the chart maps to a generization. -/
theorem exists_specializes_of_mem_closure_range {T P : Scheme.{u}} (h : T ⟶ P)
    [QuasiCompact h] [IsAffine P] {z : P} (hz : z ∈ closure (Set.range h)) :
    ∃ t : T, h t ⤳ z := by
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace h
  -- a finite affine cover of `T`
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun V : T.affineOpens ↦ (V.1 : Set T)) (fun V ↦ V.1.isOpen) (by
      intro x _
      have hx : x ∈ (⊤ : T.Opens) := trivial
      rw [← iSup_affineOpens_eq_top T] at hx
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨V, hV⟩)
  -- `z` lies in the closure of the image of one chart
  have hcover : Set.range h = ⋃ V ∈ s, h '' (V.1 : Set T) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨V, hVs, hxV⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
      exact Set.mem_iUnion₂.mpr ⟨V, hVs, x, hxV, rfl⟩
    · rintro hy
      obtain ⟨V, -, x, -, rfl⟩ := Set.mem_iUnion₂.mp hy
      exact ⟨x, rfl⟩
  rw [hcover, s.closure_biUnion] at hz
  obtain ⟨V₀, -, hzV₀⟩ := Set.mem_iUnion₂.mp hz
  -- the chart morphism, as a morphism of affine schemes
  set g : Spec Γ(T, V₀.1) ⟶ P := V₀.2.fromSpec ≫ h with hgdef
  have hrangeg : Set.range g = h '' (V₀.1 : Set T) := by
    rw [hgdef]
    have : ⇑(V₀.2.fromSpec ≫ h) = ⇑h ∘ ⇑V₀.2.fromSpec := by
      simp [Scheme.Hom.comp_base]
    rw [this, Set.range_comp, V₀.2.range_fromSpec]
  -- the chart morphism is induced by a ring map
  set φ : Γ(P, ⊤) ⟶ Γ(T, V₀.1) := g.appTop ≫ (Scheme.ΓSpecIso Γ(T, V₀.1)).hom with hφdef
  have hgSpec : g ≫ P.isoSpec.hom = Spec.map φ := by
    rw [← Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, hφdef]
  -- transport `z` to the prime spectrum
  set z' := P.isoSpec.hom z with hz'def
  have him : P.isoSpec.hom '' (h '' (V₀.1 : Set T)) = Set.range (Spec.map φ) := by
    rw [← hrangeg, ← hgSpec]
    have : ⇑(g ≫ P.isoSpec.hom) = ⇑P.isoSpec.hom ∘ ⇑g := by
      simp [Scheme.Hom.comp_base]
    rw [this, Set.range_comp]
  have hz2 : z' ∈ closure (Set.range (Spec.map φ)) := by
    rw [← him]
    exact image_closure_subset_closure_image P.isoSpec.hom.continuous ⟨z, hzV₀, rfl⟩
  -- the prime of `z'` contains the kernel of `φ`
  have hkerle : RingHom.ker φ.hom ≤ z'.asIdeal := by
    have h1 : closure (Set.range (Spec.map φ)) =
        PrimeSpectrum.zeroLocus (RingHom.ker φ.hom : Set Γ(P, ⊤)) :=
      PrimeSpectrum.closure_range_comap φ.hom
    rw [h1] at hz2
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hz2
  -- choose a prime of the chart ring contracting into the prime of `z'` (Stacks 00FK)
  have := z'.2
  obtain ⟨q, -, hq_prime, hq_le⟩ := Ideal.exists_ideal_comap_le_prime (f := φ.hom)
    z'.asIdeal (⊥ : Ideal Γ(T, V₀.1)) (by rwa [← RingHom.ker_eq_comap_bot])
  have := hq_prime
  refine ⟨V₀.2.fromSpec ⟨q, hq_prime⟩, ?_⟩
  -- the lifted point maps to the contraction of `q` in the spectrum
  have hgq : P.isoSpec.hom (h (V₀.2.fromSpec ⟨q, hq_prime⟩)) =
      Spec.map φ (⟨q, hq_prime⟩ : PrimeSpectrum Γ(T, V₀.1)) := by
    have h1 : P.isoSpec.hom (h (V₀.2.fromSpec ⟨q, hq_prime⟩)) =
        (g ≫ P.isoSpec.hom) ⟨q, hq_prime⟩ := by
      rw [hgdef, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    rw [h1, hgSpec]
  -- conclude by transporting the specialization back along the isomorphism
  have hsp : Spec.map φ (⟨q, hq_prime⟩ : PrimeSpectrum Γ(T, V₀.1)) ⤳ z' :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hq_le
  have hinv : ∀ w : P, P.isoSpec.inv (P.isoSpec.hom w) = w := by
    intro w
    rw [← Scheme.Hom.comp_apply, P.isoSpec.hom_inv_id]
    simp
  have := hsp.map P.isoSpec.inv.continuous
  rw [← hgq, hinv, hz'def, hinv] at this
  exact this

section Retrocompact

variable {X : Scheme.{u}} (W : X.Opens)

/-- **Retrocompactness** (blueprint §2.2): the inclusion of a quasi-compact open of a
quasi-separated scheme is a quasi-compact morphism. -/
theorem Scheme.Opens.quasiCompact_ι [QuasiSeparatedSpace X]
    (hW : IsCompact (W : Set X)) : QuasiCompact W.ι := by
  constructor
  intro U hU hU'
  rw [W.ι.isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range,
    Scheme.Opens.range_ι]
  exact QuasiSeparatedSpace.inter_isCompact U W hU hU' W.isOpen hW

end Retrocompact

end AlgebraicGeometry
