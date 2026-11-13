/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts
import WeilConjectures.Mathlib.RingTheory.Localization.NormTrace

/-!
# Affineness of a finite locally free norm locus

## References

* Stacks Project, Tag 03JE
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- The finite free norm criterion, transported from prime spectra to an affine open.
(compare `AlgebraicGeometry.mem_basicOpen_normAt`) -/
private theorem mem_basicOpen_norm_of_free
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π]
    {B : X.Opens} (hB : IsAffineOpen B) (a : Γ(Y, π ⁻¹ᵁ B))
    (hfree : letI := (π.app B).hom.toAlgebra
      Module.Free Γ(X, B) Γ(Y, π ⁻¹ᵁ B))
    (hfin : letI := (π.app B).hom.toAlgebra
      Module.Finite Γ(X, B) Γ(Y, π ⁻¹ᵁ B))
    {x : X} (hx : x ∈ B) :
    (letI := (π.app B).hom.toAlgebra
     x ∈ X.basicOpen (Algebra.norm Γ(X, B) a) ↔
       ∀ y, π y = x → y ∈ Y.basicOpen a) := by
  have hV : IsAffineOpen (π ⁻¹ᵁ B) := hB.preimage π
  obtain ⟨z, rfl⟩ : x ∈ Set.range hB.fromSpec := by rwa [hB.range_fromSpec]
  have hpt (w : Spec Γ(Y, π ⁻¹ᵁ B)) :
      π (hV.fromSpec w) = hB.fromSpec (PrimeSpectrum.comap (π.app B).hom w) := by
    have := congrArg (fun g ↦ g w) (IsAffineOpen.SpecMap_appLE_fromSpec π hB hV le_rfl)
    simp only [Scheme.Hom.comp_apply, Spec.map_apply] at this
    rw [← this, ← Scheme.Hom.app_eq_appLE]
  change z ∈ hB.fromSpec ⁻¹ᵁ X.basicOpen _ ↔ _
  rw [hB.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen]
  let := (π.app B).hom.toAlgebra
  refine (Algebra.norm_notMem_iff z.asIdeal a).trans ⟨fun h y hy ↦ ?_, fun h Q hQ hQz ↦ ?_⟩
  · obtain ⟨w, rfl⟩ : y ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      change π y ∈ B
      rw [hy]
      exact (Set.ext_iff.mp hB.range_fromSpec _).mp ⟨z, rfl⟩
    change w ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen a
    rw [hV.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen]
    refine h w.asIdeal w.isPrime ?_
    rw [hpt] at hy
    exact congrArg PrimeSpectrum.asIdeal (hB.fromSpec.isOpenEmbedding.injective hy)
  · have := h (hV.fromSpec ⟨Q, hQ⟩) (by
      rw [hpt]
      congr 1
      exact PrimeSpectrum.ext hQz)
    change (⟨Q, hQ⟩ : PrimeSpectrum _) ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen a at this
    rwa [hV.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen] at this

/-- A norm locus contained in an affine basic open is affine (Stacks, Tag 03JE). -/
theorem isAffineOpen_descent_norm_locus
    {V R : Scheme.{u}} (s t : R ⟶ V)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    (A : V.Opens) (hA : IsAffineOpen A) (W : V.Opens)
    (hWA : s ⁻¹' (W : Set V) ⊆ t ⁻¹' (A : Set V))
    (f : Γ(V, A)) (hfW : V.basicOpen f ≤ W)
    (U : V.Opens) (hU : U ≤ V.basicOpen f)
    (hUset : (U : Set V) = (W : Set V) ∩
      (s '' (t ⁻¹' (V.basicOpen f : Set V)ᶜ))ᶜ) :
    IsAffineOpen U := by
  let a : Γ(R, s ⁻¹ᵁ W) := t.appLE A (s ⁻¹ᵁ W) hWA f
  obtain ⟨g, hg⟩ := exists_finiteLocallyFree_norm_charts s W a
  have hga : ∀ x : V, x ∈ W →
      (x ∈ V.basicOpen g ↔ ∀ y, s y = x → t y ∈ V.basicOpen f) := by
    intro x hx
    obtain ⟨B, hBW, hxB, hB, hfree, hfin, hnorm⟩ := hg x hx
    have hres : x ∈ V.basicOpen (V.presheaf.map (homOfLE hBW).op g) ↔
        x ∈ V.basicOpen g := by
      rw [V.basicOpen_res]
      exact and_iff_right hxB
    rw [← hres, hnorm]
    rw [mem_basicOpen_norm_of_free s hB _ hfree hfin hxB]
    have heq : R.basicOpen (R.presheaf.map (homOfLE (s.preimage_mono hBW)).op a) =
        s ⁻¹ᵁ B ⊓ t ⁻¹ᵁ (V.basicOpen f) := by
      rw [R.basicOpen_res]
      dsimp [a]
      rw [Scheme.basicOpen_appLE, ← inf_assoc,
        inf_eq_left.mpr (s.preimage_mono hBW)]
    rw [heq]
    constructor
    · intro h y hy
      exact (h y hy).2
    · intro h y hy
      exact ⟨by change s y ∈ B; rw [hy]; exact hxB, h y hy⟩
  have hUg : U = V.basicOpen g := by
    apply SetLike.coe_injective
    ext x
    rw [hUset]
    constructor
    · rintro ⟨hxW, hx⟩
      apply (hga x hxW).mpr
      intro y hy
      by_contra hty
      exact hx ⟨y, hty, hy⟩
    · intro hx
      have hxW := V.basicOpen_le g hx
      refine ⟨hxW, ?_⟩
      rintro ⟨y, hty, hy⟩
      exact hty ((hga x hxW).mp hx y hy)
  let g' : Γ(V, V.basicOpen f) := V.presheaf.map (homOfLE hfW).op g
  have hg' : V.basicOpen g' = U := by
    dsimp [g']
    rw [V.basicOpen_res, ← hUg, inf_eq_right.mpr hU]
  rw [← hg']
  exact (hA.basicOpen f).basicOpen g'

end CategoryTheory.Over.DescentDatum
