/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.GlobalDimension
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import WeilConjectures.RingTheory.CohenMacaulayFreeResolution
import WeilConjectures.RingTheory.ProjectiveResolutionExtCharacterization
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularLocalMaximalCohenMacaulayFree

/-!
# Finite module resolutions over regular local rings

Every finite module over a regular local ring of dimension `d` has a projective resolution of
length at most `d`.

## Implementation details

The generators of the maximal ideal form a regular sequence (Tag 00NQ), so the depth is at
least `d`. A nonzero finite module `M` of depth `e ≤ d` has an exact sequence
`0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0` with `F_i` finite free and `K` zero or of depth `d`
(Tag 00NG), hence free (Tag 00NT). Splitting into short exact sequences bounds the Ext
projective dimension of `M` by `d - e`, and the Ext characterization (Tag 065R) gives the
resolution. The argument works in the module universe `max u v`.

## References

* [Stacks, Tag 00O7]
* [Stacks, Tags 00NQ, 00NG, 00NT, 065R]
-/

@[expose] public section

universe u v

-- An exact pair gives a short exact sequence between its two images.
open CategoryTheory CategoryTheory.Limits in
private theorem image_shortExact
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.Exact) :
    (ShortComplex.mk (image.ι T.f) (factorThruImage T.g)
      (by
        apply (cancel_mono (image.ι T.g)).mp
        simp only [Category.assoc, image.fac, zero_comp]
        exact image_ι_comp_eq_zero T.zero)).ShortExact := by
  let T' := ShortComplex.mk (image.ι T.f) T.g (image_ι_comp_eq_zero T.zero)
  have hT' : T'.Exact := by
    let φ : T ⟶ T' :=
      { τ₁ := factorThruImage T.f
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hT
  let T'' := ShortComplex.mk (image.ι T.f) (factorThruImage T.g)
    (by
      apply (cancel_mono (image.ι T.g)).mp
      simp only [Category.assoc, image.fac, zero_comp]
      exact image_ι_comp_eq_zero T.zero)
  have hT'' : T''.Exact := by
    let φ : T'' ⟶ T' :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := image.ι T.g }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hT'
  exact { exact := hT'' }

-- Induct along the images, then use the existing bounded-resolution/Ext bridge.
open CategoryTheory CategoryTheory.Limits in
private theorem resolution_of_exact_projectives
    {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R) (k : ℕ)
    (S : ComposableArrows (ModuleCat.{max u v} R) (k + 3))
    (hS : S.Exact) (hleft : IsZero (S.obj' 0))
    (hright : IsZero (S.obj' (k + 3)))
    (e : S.obj' (k + 2) ≃ₗ[R] M)
    (hproj : ∀ i : Fin (k + 1), Projective (S.obj' (i.val + 1) (by omega))) :
    ModuleCat.HasProjectiveResolutionLE M k := by
  have himages (j : ℕ) (hj : j ≤ k) :
      HasProjectiveDimensionLE (image (S.map' (j + 1) (j + 2) (by omega) (by omega))) j := by
    induction j with
    | zero =>
      let f := S.map' 1 2
      have hmono : Mono f :=
        ((hS.sc 0).exact_iff_mono (hleft.eq_of_src _ _)).mp (hS.exact 0)
      have : Projective (S.obj' 1) := hproj ⟨0, by omega⟩
      have : Mono (factorThruImage f) :=
        mono_of_mono_fac (image.fac f)
      have : IsIso (factorThruImage f) := isIso_of_mono_of_epi _
      exact hasProjectiveDimensionLT_of_iso (asIso (factorThruImage f)) 1
    | succ j ih =>
      have hprev := ih (by omega)
      have hstep := image_shortExact (hS.sc (j + 1) (by omega))
        (hS.exact (j + 1) (by omega))
      have : Projective (S.obj' (j + 2) (by omega)) := hproj ⟨j + 1, by omega⟩
      exact hstep.hasProjectiveDimensionLT_X₃ (j + 1) hprev
        (hasProjectiveDimensionLT_of_ge _ 1 (j + 2) (by omega))
  have hlast := himages k le_rfl
  let g := S.map' (k + 1) (k + 2)
  have hepi : Epi g :=
    ((hS.sc (k + 1)).exact_iff_epi (hright.eq_of_tgt _ _)).mp (hS.exact (k + 1))
  have : Epi (image.ι g) :=
    epi_of_epi_fac (image.fac g)
  have : IsIso (image.ι g) := isIso_of_mono_of_epi _
  have : HasProjectiveDimensionLE (S.obj' (k + 2)) k :=
    hasProjectiveDimensionLT_of_iso (asIso (image.ι g)) (k + 1)
  have : HasProjectiveDimensionLE M k :=
    hasProjectiveDimensionLT_of_iso e.toModuleIso (k + 1)
  apply (ModuleCat.hasProjectiveResolutionLE_iff_ext_vanishing M k).1.mpr
  intro Y
  let := HasExt.standard (ModuleCat.{max u v} R)
  exact HasProjectiveDimensionLT.subsingleton M (k + 1) (k + 1) le_rfl Y

namespace IsRegularLocalRing

/-- Every finite module over a regular local ring of dimension `d` has a projective
resolution of length at most `d`. -/
theorem finiteModule_hasProjectiveResolutionLE
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    ∀ M : ModuleCat.{max u v} R, Module.Finite R M →
      ModuleCat.HasProjectiveResolutionLE M d := open CategoryTheory CategoryTheory.Limits in by
  classical
  intro M hM
  have : Module.Finite R M := hM
  by_cases hzero : Subsingleton M
  · have : Subsingleton M := hzero
    have hz : IsZero M := ModuleCat.isZero_of_subsingleton M
    have : Projective M := hz.projective
    refine ⟨ProjectiveResolution.self M, ?_⟩
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hzero
    have hrank : (IsLocalRing.maximalIdeal R).spanFinrank = d := by
      have h := spanFinrank_maximalIdeal (R := R)
      rw [hd] at h
      exact_mod_cast h
    obtain ⟨s, hslen, hsspan⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank
        (p := (IsLocalRing.maximalIdeal R : Submodule R R))
        (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
    let rs := s.toList
    have hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal R := by
      simpa [Ideal.ofList, rs] using hsspan
    have hlen : rs.length = d := by simpa [rs, hrank] using hslen
    have hrs : IsLocalRing.IsRegularSystemOfParameters rs :=
      ⟨hspan, by rw [hlen, hd]⟩
    have hreg := (isRegular_and_quotients_of_generators R d hd rs hrs).1
    have hcm : (d : ℕ∞) ≤ IsLocalRing.depth (R := R) R := by
      unfold IsLocalRing.depth Ideal.depth
      split_ifs with hm
      · exact le_top
      · apply le_sSup
        refine ⟨rs, hreg, ?_, ?_⟩
        · intro x hx
          rw [← hspan]
          exact Ideal.subset_span hx
        · rw [hlen]
    obtain ⟨e, _, _, S, hS, hleft, hright, ⟨eM⟩, hF, hK⟩ :=
      IsLocalRing.exists_finite_free_resolution_to_maximalCohenMacaulay M d hd hcm
    obtain ⟨hKfin, hKdepth⟩ := hK
    let K := S.obj' 1 (by omega)
    have : Module.Finite R K := hKfin
    have hKproj : Projective K := by
      rcases hKdepth with hKzero | hKdepth
      · have : Subsingleton K := hKzero
        exact (ModuleCat.isZero_of_subsingleton K).projective
      · have : Module.Free R K :=
          (free_of_depth_eq_ringKrullDim R K d hd hKdepth).1
        infer_instance
    have hproj : ∀ i : Fin (d - e + 1),
        Projective (S.obj' (i.val + 1) (by omega)) := by
      intro i
      by_cases hi : i.val = 0
      · simpa [K, hi] using hKproj
      · have hj : i.val - 1 < d - e := by omega
        have hfree := (hF ⟨i.val - 1, hj⟩).1
        have heq : i.val - 1 + 2 = i.val + 1 := by omega
        have : Module.Free R (S.obj' (i.val + 1) (by omega)) := by
          have hidx : (⟨i.val + 1, by omega⟩ : Fin (d - e + 4)) =
              ⟨i.val - 1 + 2, by omega⟩ := Fin.ext heq.symm
          change Module.Free R (S.obj ⟨i.val + 1, by omega⟩)
          rw [hidx]
          exact hfree
        infer_instance
    obtain ⟨P, hP⟩ := resolution_of_exact_projectives M (d - e) S
      hS hleft hright eM hproj
    exact ⟨P, fun i hi ↦ hP i (lt_of_le_of_lt (Nat.sub_le d e) hi)⟩

end IsRegularLocalRing
