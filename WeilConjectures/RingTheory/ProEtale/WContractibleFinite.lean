/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.RingTheory.ProEtale.WLocalFinite
public import WeilConjectures.RingTheory.ProEtale.ClosedPointsLocallyInjective
public import WeilConjectures.Topology.ExtremallyDisconnectedLocal
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Finite finitely presented algebras over w-contractible rings

## Main results

- `IsWContractibleRing.of_finite`: a module-finite, finitely presented algebra over a
  w-contractible ring is w-contractible.
-/

@[expose] public section

universe u

open PrimeSpectrum Topology TopologicalSpace

/-- For a w-local ring `R`, the closed points of `Spec R` are homeomorphic to the connected
components of `Spec R` (`WLocalSpace.isHomeomorph_connectedComponents_closedPoints`). -/
noncomputable def IsWLocalRing.closedPointsHomeomorph (R : Type*) [CommRing R] [IsWLocalRing R] :
    closedPoints (PrimeSpectrum R) ≃ₜ ConnectedComponents (PrimeSpectrum R) :=
  IsHomeomorph.homeomorph _ (WLocalSpace.isHomeomorph_connectedComponents_closedPoints _)

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A module-finite, finitely presented algebra `B` over a w-contractible ring `A` is
w-contractible.

`B` is w-strictly-local by `IsWStrictlyLocalRing.of_finite`. The closed points of `Spec B` are
the preimage of the closed points of `Spec A`, and the induced map between these profinite sets
is open (by Chevalley's theorem, images of basic opens are constructible, and constructible sets
are clopen on the closed points) and locally injective
(`IsWStrictlyLocalRing.exists_injOn_closedPoints`). Hence the closed points of `Spec B`, which
are homeomorphic to `π₀ (Spec B)`, form an extremally disconnected space
(`ExtremallyDisconnected.of_forall_exists_injOn`). -/
theorem IsWContractibleRing.of_finite [IsWContractibleRing A] [Module.Finite A B]
    [Algebra.FinitePresentation A B] : IsWContractibleRing B := by
  have hB : IsWStrictlyLocalRing B := IsWStrictlyLocalRing.of_finite (A := A)
  have hcl (y : PrimeSpectrum B) : y ∈ closedPoints (PrimeSpectrum B) ↔
      comap (algebraMap A B) y ∈ closedPoints (PrimeSpectrum A) := by
    simp only [mem_closedPoints_iff, isClosed_singleton_iff_isMaximal, comap_asIdeal]
    exact ⟨fun _ ↦ Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _,
      fun h ↦ Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h⟩
  have := IsWContractibleRing.extremallyDisconnected_connectedComponents (R := A)
  have : ExtremallyDisconnected (closedPoints (PrimeSpectrum A)) :=
    extremallyDisconnected_of_homeo (IsWLocalRing.closedPointsHomeomorph A).symm
  have : T2Space (closedPoints (PrimeSpectrum A)) :=
    (IsWLocalRing.closedPointsHomeomorph A).isEmbedding.t2Space
  let φ : closedPoints (PrimeSpectrum B) → closedPoints (PrimeSpectrum A) :=
    fun y ↦ ⟨comap (algebraMap A B) y, (hcl y).1 y.2⟩
  have hφ : Continuous φ := ((continuous_comap _).comp continuous_subtype_val).subtype_mk _
  have hφopen : IsOpenMap φ := by
    refine (isTopologicalBasis_basic_opens.isInducing
      Topology.IsInducing.subtypeVal).isOpenMap_iff.2 ?_
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    have himage : φ '' (Subtype.val ⁻¹' (basicOpen b : Set (PrimeSpectrum B))) =
        Subtype.val ⁻¹' (comap (algebraMap A B) '' basicOpen b) := by
      ext ⟨z, hz⟩
      simp only [Set.mem_image, Set.mem_preimage, Subtype.exists, φ, Subtype.mk.injEq]
      constructor
      · rintro ⟨y, -, hyb, rfl⟩
        exact ⟨y, hyb, rfl⟩
      · rintro ⟨y, hyb, rfl⟩
        exact ⟨y, (hcl y).2 hz, hyb, rfl⟩
    rw [himage]
    exact (IsConstructible.isClopen_preimage_val WLocalSpace.isClosed_closedPoints
      (isConstructible_comap_image (RingHom.finitePresentation_algebraMap.2 inferInstance)
        isConstructible_basicOpen)).isOpen
  have : ExtremallyDisconnected (closedPoints (PrimeSpectrum B)) := by
    refine ExtremallyDisconnected.of_forall_exists_injOn hφ fun y ↦ ?_
    have : y.1.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal _).1 y.2
    obtain ⟨s, hs, hinj⟩ := IsWStrictlyLocalRing.exists_injOn_closedPoints (A := A) y.1.asIdeal
    refine ⟨Subtype.val ⁻¹' (basicOpen s : Set (PrimeSpectrum B)),
      (basicOpen s).2.preimage continuous_subtype_val, hs, ?_, fun V _ hV ↦ hφopen V hV⟩
    intro y₁ hy₁ y₂ hy₂ h
    exact Subtype.ext (hinj y₁ y₂ ((isClosed_singleton_iff_isMaximal _).1 y₁.2)
      ((isClosed_singleton_iff_isMaximal _).1 y₂.2) hy₁ hy₂ (congrArg Subtype.val h))
  exact { toIsWStrictlyLocalRing := hB
          extremallyDisconnected_connectedComponents :=
            extremallyDisconnected_of_homeo (IsWLocalRing.closedPointsHomeomorph B) }
