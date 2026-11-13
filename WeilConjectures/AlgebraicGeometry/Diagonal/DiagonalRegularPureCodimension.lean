/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular.RegularImmersionPureCodimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion

/-!
# The smooth diagonal with the chapter's pure-codimension convention

The chapter's definition concerns positive codimension and separated finite-type schemes
over a field. Unlike the upstream affine-local predicate, it records stalk dimensions as
well as regular generators. The current blueprint_update removes the old tangent-bundle
conclusion. The rank-zero clopen case used by the consumer is expressed there directly.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The diagonal of a separated smooth map of pure positive relative dimension is regular
of that pure codimension, in the chapter's fixed separated finite-type field setting. -/
theorem diagonal_isRegularImmersionOfPureCodimension
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (hd : 1 ≤ d) [SmoothOfRelativeDimension d f] :
    IsRegularImmersionOfPureCodimension
      (pullback.fst f f ≫ f ≫ aY) (pullback.diagonal f) d := by
  have : NeZero d := ⟨by omega⟩
  let i := pullback.diagonal f
  let W := pullback f f
  have : IsRegularImmersion d i := inferInstance
  have : IsLocallyNoetherian W :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f ≫ aY)
  have hstalk (z : X) : ∃ r : List (W.presheaf.stalk (i z)),
      r.length = d ∧ RingTheory.Sequence.IsRegular (W.presheaf.stalk (i z)) r ∧
        Ideal.ofList r = RingHom.ker (i.stalkMap z).hom := by
    obtain ⟨U, hxU, r, hr, hreg, hI⟩ :=
      IsRegularImmersion.exists_isWeaklyRegular_generators (c := d) (i := i) (i z)
    let := W.presheaf.algebra_section_stalk ⟨i z, hxU⟩
    have := U.2.isLocalization_stalk ⟨i z, hxU⟩
    have : Module.Flat Γ(W, U.1) (W.presheaf.stalk (i z)) :=
      IsLocalization.flat _ (U.2.primeIdealOf ⟨i z, hxU⟩).asIdeal.primeCompl
    have hsupp : i z ∈ W.zeroLocus (U := U.1) (i.ker.ideal U) :=
      (Scheme.IdealSheafData.mem_support_iff_of_mem hxU).mp
        (i.range_subset_ker_support ⟨z, rfl⟩)
    refine ⟨r.map (algebraMap Γ(W, U.1) (W.presheaf.stalk (i z))),
      by simpa using hr, ?_, ?_⟩
    · refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr
        hreg.of_flat
      intro _ hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      have : s ∈ i.ker.ideal U := hI ▸ Ideal.subset_span hs
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact (W.mem_basicOpen _ _ hxU).not.mp ((W.mem_zeroLocus_iff _ _).mp hsupp s this)
    · rw [← Ideal.map_ofList, hI,
        show algebraMap Γ(W, U.1) _ = (W.presheaf.germ U (i z) hxU).hom from rfl,
        ← i.ker_stalkMap U z hxU]
  refine ⟨hd, ?_, ?_⟩
  · intro z
    obtain ⟨r, hr, hreg, hker⟩ := hstalk z
    have key := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular r hreg
    rw [hker, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z)), hr] at key
    exact key.symm
  · intro z
    obtain ⟨r, hr, hreg, hker⟩ := hstalk z
    subst d
    refine ⟨r.get, ?_, ?_⟩
    · simpa only [List.ofFn_get] using hreg
    · have hrange : Set.range r.get = {x | x ∈ r} := by
        ext x
        simp only [Set.mem_range, Set.mem_ofPred_eq, List.mem_iff_get]
      simpa only [hrange, Ideal.ofList] using hker

end AlgebraicGeometry
