/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.RingTheory.WellOrderedPresentationKernelFiltration
import WeilConjectures.RingTheory.ProjectiveResolutionAugmentationKernel

/-!
# Projective presentations for well-ordered unions

Projective presentations for the successor step of the well-ordered filtration argument.

## Implementation details

Instead of free presentations of the stages, we use the projective presentations supplied by
`hquot`, which allows full universe generality. The kernel of the presentation inherits a
well-ordered filtration whose quotients are augmentation kernels of the chosen resolutions.

## References

* [Stacks Project, Lemma 0D1U](https://stacks.math.columbia.edu/tag/0D1U)
-/

@[expose] public section

universe u v w

namespace ModuleCat

open CategoryTheory

private theorem resolution_bound_of_isZero
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (n : ℕ)
    (hM : CategoryTheory.Limits.IsZero M) : HasProjectiveResolutionLE M n := by
  have := hM.projective
  refine ⟨ProjectiveResolution.self M, fun i hi ↦ ?_⟩
  exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

private theorem resolution_bound_of_iso
    {R : Type u} [CommRing R] {M N : ModuleCat.{v} R} (n : ℕ)
    (e : M ≅ N) (hN : HasProjectiveResolutionLE N n) :
    HasProjectiveResolutionLE M n := by
  obtain ⟨P, hP⟩ := hN
  refine ⟨{
    complex := P.complex
    projective := P.projective
    π := P.π ≫ (ChainComplex.single₀ (ModuleCat.{v} R)).map e.inv
    quasiIso := inferInstance }, hP⟩

-- The names of the hypotheses bound inside hIH are kept for interface compatibility.
set_option linter.unusedVariables false in
/-- Let `M` be the union of a well-ordered filtration `F` whose successive quotients have
projective resolutions of length at most `n + 1`. Assuming the statement `hIH` in length `n`,
there is a short exact sequence `0 → K → P → M → 0` with `P` projective and `K` admitting a
projective resolution of length at most `n`. -/
theorem exists_shortExact_projective_middle_of_wellOrderedUnion_succ
    {R : Type u} [CommRing R] (n : ℕ)
    (hIH : ∀ (M : ModuleCat.{v} R) {E : Type w} [LinearOrder E]
      [IsWellOrder E (· < ·)] (F : E → Submodule R M) (hF : Monotone F)
      (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
      (hquot : ∀ e : E, HasProjectiveResolutionLE
        (ModuleCat.of R ((F e) ⧸
          ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) n),
      HasProjectiveResolutionLE M n)
    (M : ModuleCat.{v} R) {E : Type w} [LinearOrder E]
    [IsWellOrder E (· < ·)] (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (hquot : ∀ e : E, HasProjectiveResolutionLE
      (ModuleCat.of R ((F e) ⧸
        ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) (n + 1)) :
    ∃ S : ShortComplex (ModuleCat.{v} R), S.X₃ = M ∧ S.ShortExact ∧
      Projective S.X₂ ∧ HasProjectiveResolutionLE S.X₁ n := by
  classical
  choose P hP using hquot
  obtain ⟨S, hM, hS, hproj, G, hG, hGcover, hGquot⟩ :=
    exists_projective_presentation_kernel_filtration M F hF hcover P
  refine ⟨S, hM, hS, hproj, hIH S.X₁ G hG hGcover ?_⟩
  intro e
  rcases hGquot e with hzero | hiso
  · exact resolution_bound_of_isZero _ n hzero
  · obtain ⟨a⟩ := hiso
    exact resolution_bound_of_iso n a
      (hasProjectiveResolutionLE_augmentation_kernel n (P e) (hP e))

end ModuleCat
