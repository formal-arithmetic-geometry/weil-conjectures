/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Connected.Basic

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ConnectedGenericFibreTrait

/-!
# A connected open containing two sections over a trait

Source: Stacks Project, More on Morphisms, Tag 055Q,
`lemma-connected-along-section-open-neighbourhood`, final paragraph, and Tag 055J,
`lemma-connected-flat-over-dvr`.
(blueprint: lem-trf-flat-trait-two-section-connected-open)
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

/-- Two sections through the same component of a reduced closed fibre over a DVR factor
through a connected open with exactly that closed fibre component and connected generic fibre.
Both generic section points therefore lie in the same component of the generic fibre.

Source: Stacks Project, Tag 055Q, `lemma-connected-along-section-open-neighbourhood`,
final paragraph; Tag 055J, `lemma-connected-flat-over-dvr`.

Proof:
1. The DVR is noetherian, so its spectrum is a noetherian scheme. Mathlib's proved
   instance from local finite presentation to local finite type, together with
   quasi-compactness, makes X noetherian. Every subspace is consequently noetherian.
2. In the closed point-set fibre F, let D be the component of the first special section
   point. Its complement in F is closed because components of a noetherian space are open.
   Since F is closed in X, this complement has closed image C in X. Put U = X minus C.
   Then D is contained in U and U intersects F exactly in D.
3. Take W to be the component of the first special section point in U. Noetherian spaces
   are locally connected, so W is open in X. The connected set D lies in W by maximality
   of connected components, hence W intersects F exactly in D. This component W is
   connected and nonempty.
4. Each section's special point belongs to W. Every point of the spectrum of a local ring
   specializes to its closed point, so continuity and openness put each section's entire
   image in W. The open-immersion lifting property factors both sections through W.
5. The composite h of W.ι with f is flat. The induced map from its closed fibre to the
   closed fibre of f is an open immersion, given by the pullback map induced by W.ι and
   identities on the base and residue-field spectrum. Its source is therefore reduced.
6. Apply the connected-generic-fibre theorem of Tag 055J to h. The continuous image of
   this connected generic fibre in X is preconnected and lies in the generic fibre of f.
   Each factored section gives a point of this image: use its section equation and the
   inverse of h.fiberHomeo at the zero prime. Thus both generic section points lie in
   that preconnected set. Maximality of the connected component containing the first
   point gives the assertion for the second point.

(blueprint: lem-trf-flat-trait-two-section-connected-open) -/
theorem exists_connected_open_two_sections_of_flat_trait
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f]
    (σ τ : Spec (.of R) ⟶ X)
    (hσ : σ ≫ f = 𝟙 (Spec (.of R))) (hτ : τ ≫ f = 𝟙 (Spec (.of R)))
    [IsReduced (f.fiber (closedPoint R))]
    (hτD : τ (closedPoint R) ∈
      connectedComponentIn (f ⁻¹' {closedPoint R}) (σ (closedPoint R))) :
    (∃ W : X.Opens,
      connectedComponentIn (f ⁻¹' {closedPoint R}) (σ (closedPoint R)) ⊆ (W : Set X) ∧
      (W : Set X) ∩ f ⁻¹' {closedPoint R} =
        connectedComponentIn (f ⁻¹' {closedPoint R}) (σ (closedPoint R)) ∧
      ConnectedSpace W.toScheme ∧
      (∃ σW : Spec (.of R) ⟶ W.toScheme, σW ≫ W.ι = σ) ∧
      (∃ τW : Spec (.of R) ⟶ W.toScheme, τW ≫ W.ι = τ) ∧
      Flat (W.ι ≫ f) ∧
      IsReduced ((W.ι ≫ f).fiber (closedPoint R)) ∧
      ConnectedSpace ((W.ι ≫ f).fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R))) ∧
    τ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈
      connectedComponentIn (f ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)})
        (σ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  -- Isolate the chosen component of the closed fibre.
  let F : Set X := f ⁻¹' {closedPoint R}
  have hσs : σ (closedPoint R) ∈ F := by
    change (σ ≫ f) (closedPoint R) = closedPoint R
    rw [hσ]
    rfl
  let x : F := ⟨σ (closedPoint R), hσs⟩
  let D : Set X := connectedComponentIn F (σ (closedPoint R))
  have hD : D = Subtype.val '' connectedComponent x :=
    connectedComponentIn_eq_image hσs
  have hF : IsClosed F := (isClosed_singleton_closedPoint R).preimage f.continuous
  let C : Set X := Subtype.val '' (connectedComponent x)ᶜ
  have hC : IsClosed C := hF.isClosedEmbedding_subtypeVal.isClosedMap _
    (TopologicalSpace.NoetherianSpace.isOpen_connectedComponent x).isClosed_compl
  have hDU : D ⊆ Cᶜ := by
    rw [hD]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    exact hw (Subtype.val_injective hwz ▸ hz)
  have hUF : Cᶜ ∩ F = D := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzC, hzF⟩
      rw [hD]
      refine ⟨⟨z, hzF⟩, ?_, rfl⟩
      by_contra hz
      exact hzC ⟨⟨z, hzF⟩, hz, rfl⟩
    · exact fun z hz ↦ ⟨hDU hz, connectedComponentIn_subset F _ hz⟩
  have hxD : σ (closedPoint R) ∈ D := mem_connectedComponentIn hσs
  let W : X.Opens := ⟨connectedComponentIn Cᶜ (σ (closedPoint R)),
    hC.isOpen_compl.connectedComponentIn⟩
  have hDW : D ⊆ (W : Set X) :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn hxD hDU
  have hWF : (W : Set X) ∩ F = D := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hUF.subset ⟨connectedComponentIn_subset Cᶜ _ hz.1, hz.2⟩
    · exact fun z hz ↦ ⟨hDW hz, connectedComponentIn_subset F _ hz⟩
  have : ConnectedSpace W.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr (hDU hxD))
  -- An open containing the closed section point contains the whole section.
  have hfactor (φ : Spec (.of R) ⟶ X) (hφ : φ (closedPoint R) ∈ W) :
      ∃ φW : Spec (.of R) ⟶ W.toScheme, φW ≫ W.ι = φ := by
    have hrange : Set.range φ ⊆ Set.range W.ι := by
      rintro _ ⟨z, rfl⟩
      have hz : φ z ∈ W :=
        ((specializes_closedPoint z).map φ.continuous).mem_open W.isOpen hφ
      exact ⟨⟨φ z, hz⟩, rfl⟩
    exact ⟨IsOpenImmersion.lift W.ι φ hrange, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨σW, hσW⟩ := hfactor σ (hDW hxD)
  obtain ⟨τW, hτW⟩ := hfactor τ (hDW hτD)
  let h := W.ι ≫ f
  have : Flat h := inferInstance
  have : IsReduced (h.fiber (closedPoint R)) := by
    let a := (Spec (.of R)).fromSpecResidueField (closedPoint R)
    let j : h.fiber (closedPoint R) ⟶ f.fiber (closedPoint R) :=
      Limits.pullback.map h a f a W.ι (𝟙 _) (𝟙 _) (by simp [h]) (by simp)
    exact isReduced_of_isOpenImmersion j
  have : ConnectedSpace (h.fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) :=
    connectedSpace_generic_fibre_of_flat_trait h
  refine ⟨⟨W, hDW, hWF, inferInstance, ⟨σW, hσW⟩, ⟨τW, hτW⟩,
    inferInstance, inferInstance, inferInstance⟩, ?_⟩
  -- Compare generic section points inside the connected generic fibre of W.
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let g : h.fiber η ⟶ X := h.fiberι η ≫ W.ι
  have hmem (φ : Spec (.of R) ⟶ X) (φW : Spec (.of R) ⟶ W.toScheme)
      (hφW : φW ≫ W.ι = φ) (hφ : φ ≫ f = 𝟙 _) : φ η ∈ Set.range g := by
    have hpoint : h (φW η) = η := by
      change (φW ≫ (W.ι ≫ f)) η = η
      rw [← Category.assoc, hφW, hφ]
      rfl
    refine ⟨(h.fiberHomeo η).symm ⟨φW η, hpoint⟩, ?_⟩
    change W.ι (h.fiberι η ((h.fiberHomeo η).symm ⟨φW η, hpoint⟩)) = φ η
    rw [Scheme.Hom.fiberι_fiberHomeo_symm]
    exact congrArg (fun k : Spec (.of R) ⟶ X ↦ k η) hφW
  have hgF : Set.range g ⊆ f ⁻¹' {η} := by
    rintro _ ⟨z, rfl⟩
    change h (h.fiberι η z) = η
    exact (h.fiberHomeo η z).2
  exact (isPreconnected_range g.continuous).subset_connectedComponentIn
    (hmem σ σW hσW hσ) hgF (hmem τ τW hτW hτ)

end AlgebraicGeometry
