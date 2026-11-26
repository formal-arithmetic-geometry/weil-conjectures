/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension

/-!
# Localization and finite global dimension

Localization preserves bounds on the lengths of projective resolutions, and hence finite global
dimension.

## Implementation details

A projective resolution localizes term by term to a projective resolution of the same length,
by exactness of localization and Stacks 05A3. A module over the localized ring is isomorphic to
its own localization as an `R`-module, which gives the global dimension bound.

## References

* [Stacks, Tag 00O8]
* [Stacks, Tags 00CS, 05A3]
-/

@[expose] public section

universe u v

namespace Ring

private theorem resolution_bound_of_iso
    {A : Type u} [CommRing A] {M N : ModuleCat.{max u v} A}
    (e : CategoryTheory.Iso M N) {n : ℕ} (h : ModuleCat.HasProjectiveResolutionLE M n) :
    ModuleCat.HasProjectiveResolutionLE N n := by
  obtain ⟨P, hP⟩ := h
  exact ⟨{ complex := P.complex
           projective := P.projective
           π := CategoryTheory.CategoryStruct.comp P.π
             ((ChainComplex.single₀ _).map e.hom) }, hP⟩

private theorem localized_resolution_bound
    (R : Type u) [CommRing R] (S : Submonoid R) (n : ℕ)
    (M : ModuleCat.{max u v} R) (h : ModuleCat.HasProjectiveResolutionLE M n) :
    ModuleCat.HasProjectiveResolutionLE
      (ModuleCat.of (Localization S) (LocalizedModule S M)) n := by
  obtain ⟨P, hP⟩ := h
  have hloc : ModuleCat.HasProjectiveResolutionLE (M.localizedModule S) n := by
    refine ⟨(ModuleCat.localizedModuleFunctor S).mapProjectiveResolution P, ?_⟩
    intro i hi
    exact (ModuleCat.localizedModuleFunctor S).map_isZero (hP i hi)
  exact resolution_bound_of_iso
    (Shrink.linearEquiv (Localization S) (LocalizedModule S M)).toModuleIso hloc

/-- Localization preserves bounds on projective resolution lengths and global dimension. -/
theorem localization_preserves_projective_and_global_dimension
    (R : Type u) [CommRing R] (S : Submonoid R) (n : ℕ) :
    (∀ M : ModuleCat.{max u v} R,
      ModuleCat.HasProjectiveResolutionLE M n →
        ModuleCat.HasProjectiveResolutionLE
          (ModuleCat.of (Localization S) (LocalizedModule S M)) n) ∧
    (HasGlobalDimensionLE.{u, max u v} R n →
      HasGlobalDimensionLE.{u, max u v} (Localization S) n) ∧
    (∀ h : HasFiniteGlobalDimension.{u, max u v} R,
      ∃ hS : HasFiniteGlobalDimension.{u, max u v} (Localization S),
        globalDimension.{u, max u v} (Localization S) hS ≤
          globalDimension.{u, max u v} R h) := by
  classical
  have hres := localized_resolution_bound R S n
  have hglobal (k : ℕ) (h : HasGlobalDimensionLE.{u, max u v} R k) :
      HasGlobalDimensionLE.{u, max u v} (Localization S) k := by
    intro M
    let : Module R M := Module.compHom M (algebraMap R (Localization S))
    let : IsScalarTower R (Localization S) M := IsScalarTower.of_algebraMap_smul
      (fun r m ↦ rfl)
    let MR := ModuleCat.of R M
    have hMR := localized_resolution_bound R S k MR
      ((ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE MR k).2 (h MR))
    let := isLocalizedModule_id S M (Localization S)
    exact (ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE _ k).1
      (resolution_bound_of_iso
        ((IsLocalizedModule.iso S (LinearMap.id : M →ₗ[R] M)).extendScalarsOfIsLocalization
          S (Localization S)).toModuleIso hMR)
  refine ⟨hres, hglobal n, ?_⟩
  intro h
  have hb := hglobal (globalDimension R h) (Nat.find_spec h)
  let hS : HasFiniteGlobalDimension.{u, max u v} (Localization S) :=
    ⟨globalDimension R h, hb⟩
  exact ⟨hS, Nat.find_min' hS hb⟩

end Ring
