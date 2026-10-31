/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Topology.SpectralClosedSubspace

/-!
# Closed points and connected components of w-local spaces

Source: blueprint `sec-proetale-coefficients/sk-def-pe-wlocal/det-pe-wlocal-components.md`;
Stacks Project, Tags 0968 and 096A (blueprint: det-pe-wlocal-components).
-/

@[expose] public section

universe u v

open Topology

namespace WLocalSpace

private theorem component_eq_generalizations {X : Type*} [TopologicalSpace X]
    [WLocalSpace X] (c : closedPoints X) :
    connectedComponent c.val = {x : X | x ⤳ c.val} := by
  ext x
  constructor
  · intro hx
    obtain ⟨d, hd, hxd⟩ := exists_isClosed_specializes x
    have hdc : d = c.val := closedPoints_eq_of_mk_eq (mem_closedPoints_iff.mpr hd) c.property
      (hxd.connectedComponents_mk_eq.symm.trans (ConnectedComponents.coe_eq_coe'.mpr hx))
    exact hdc ▸ hxd
  · intro hxc
    exact ConnectedComponents.coe_eq_coe'.mp hxc.connectedComponents_mk_eq

private theorem unique_specialization_of_unique_component {X : Type*} [TopologicalSpace X]
    [SpectralSpace X]
    (h : ∀ x : X, ∃! c : closedPoints X, c.val ∈ connectedComponent x) :
    ∀ x : X, ∃! c : closedPoints X, x ⤳ c.val := by
  intro x
  obtain ⟨c, hc, hxc⟩ := exists_isClosed_specializes x
  refine ⟨⟨c, mem_closedPoints_iff.mpr hc⟩, hxc, ?_⟩
  intro d hxd
  obtain ⟨e, he, hue⟩ := h x
  exact (hue d (ConnectedComponents.coe_eq_coe'.mp hxd.connectedComponents_mk_eq.symm)).trans
    (hue ⟨c, mem_closedPoints_iff.mpr hc⟩
      (ConnectedComponents.coe_eq_coe'.mp hxc.connectedComponents_mk_eq.symm)).symm

private theorem wLocal_iff_unique_component {X : Type*} [TopologicalSpace X]
    [SpectralSpace X] (hclosed : IsClosed (closedPoints X)) :
    WLocalSpace X ↔ ∀ x : X, ∃! c : closedPoints X, c.val ∈ connectedComponent x := by
  constructor
  · intro hW x
    have : WLocalSpace X := hW
    obtain ⟨c, hc, hxc⟩ := exists_isClosed_specializes x
    refine ⟨⟨c, mem_closedPoints_iff.mpr hc⟩,
      ConnectedComponents.coe_eq_coe'.mp hxc.connectedComponents_mk_eq.symm, ?_⟩
    intro d hd
    apply Subtype.ext
    exact closedPoints_eq_of_mk_eq d.property (mem_closedPoints_iff.mpr hc)
      ((ConnectedComponents.coe_eq_coe'.mpr hd).trans hxc.connectedComponents_mk_eq)
  · intro h
    have hu := unique_specialization_of_unique_component h
    exact {
      eq_of_specializes := fun {x c d} hc hd hxc hxd ↦
        congrArg Subtype.val ((hu x).unique (y₁ := ⟨c, mem_closedPoints_iff.mpr hc⟩)
          (y₂ := ⟨d, mem_closedPoints_iff.mpr hd⟩) hxc hxd)
      isClosed_closedPoints := hclosed }

/-- The four assertions about components of a spectral space with closed closed-point locus.
Profinite means compact, Hausdorff and totally disconnected. The retraction is characterized by
specialization to its value, so its existential presentation specifies the canonical map.
For affine schemes we use their underlying Zariski spaces `PrimeSpectrum R`; the localization
map on these spaces is `PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))`.

Source: blueprint `det-pe-wlocal-components`; Stacks Project, Tags 0968, 096A, 0905 and 00E3
(blueprint: det-pe-wlocal-components).

Proof:
1. By `lem-weil-pbc-spectral-closed-subspace`, the closed-point subspace is spectral.
Its singletons are closed, so it has no nontrivial specializations.
2. Apply the proved source-library instance `SpectralSpace.totallySeparatedSpace` to
this T1 spectral space. This is the Stacks 0905 argument: compact opens are constructibly
closed and specialization-stable, hence closed, and the compact-open basis separates points.
3. Total separation gives Hausdorffness and total disconnectedness; spectrality gives
compactness, proving the first assertion.
4. Apply `lem-sc-quasi-compact-kolmogorov-closed-point` to the closure of each singleton.
It supplies a closed specialization. A singleton closure is connected, since every nonempty
relatively open subset contains its generic point; thus specializations remain in a component.
5. Under uniqueness, use
`lem-weil-pbc-w-local-closed-points-components-homeomorphism` to identify closed points with
components. Compose the continuous component quotient with the inverse homeomorphism to
obtain the retraction. Step 4 identifies its value with the unique closed specialization.
It fixes closed points; its fibres are their components and exactly their generalizations.
Transport the profinite topology of step 3 through the homeomorphism.
6. Conversely, step 4 provides a closed specialization in the component of each point.
Uniqueness of the closed point in that component gives uniqueness of the specialization.
This proves agreement of `sk-def-pe-wlocal` and `def-weil-pbc-w-local`, retaining closedness
of the closed-point locus, both for spaces and for affine spectra.
7. For a maximal ideal m, `def-weil-pbc-localization-at-prime` and
`lem-weil-pbc-localization-spectrum-embedding` identify the image of Spec R_m with primes
contained in m. The Zariski identity closure({p}) = V(p) identifies these with the
 generalizations of m, hence with its component by step 5. -/
theorem spectralSpace_closedPoints_components
    (T : Type u) [TopologicalSpace T] [SpectralSpace T]
    (hclosed : IsClosed (closedPoints T)) :
    (CompactSpace (closedPoints T) ∧ T2Space (closedPoints T) ∧
      TotallyDisconnectedSpace (closedPoints T)) ∧
    ((∀ x : T, ∃! c : closedPoints T, x ⤳ c.val) →
      (∃ r : T → closedPoints T,
        Continuous r ∧ (∀ x : T, x ⤳ (r x).val) ∧
        (∀ c : closedPoints T, r c.val = c) ∧
        ∀ c : closedPoints T,
          r ⁻¹' {c} = connectedComponent c.val ∧
          connectedComponent c.val = {x : T | x ⤳ c.val}) ∧
      IsHomeomorph (ConnectedComponents.mk ∘ (Subtype.val : closedPoints T → T)) ∧
      CompactSpace (ConnectedComponents T) ∧ T2Space (ConnectedComponents T) ∧
      TotallyDisconnectedSpace (ConnectedComponents T)) ∧
    ((∀ x : T, ∃! c : closedPoints T, c.val ∈ connectedComponent x) →
      ∀ x : T, ∃! c : closedPoints T, x ⤳ c.val) ∧
    (WLocalSpace T ↔ ∀ x : T, ∃! c : closedPoints T, c.val ∈ connectedComponent x) ∧
    (∀ (R : Type v) [CommRing R],
      IsWLocalRing R ↔ IsClosed (closedPoints (PrimeSpectrum R)) ∧
        ∀ x : PrimeSpectrum R,
          ∃! c : closedPoints (PrimeSpectrum R), c.val ∈ connectedComponent x) ∧
    (∀ (R : Type v) [CommRing R] [IsWLocalRing R] (m : Ideal R) [m.IsMaximal],
      connectedComponent (⟨m, inferInstance⟩ : PrimeSpectrum R) =
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m)))) := by
  classical
  have hS : SpectralSpace (closedPoints T) := (spectral_closed_subspace _ hclosed).1
  have hprof : CompactSpace (closedPoints T) ∧ T2Space (closedPoints T) ∧
      TotallyDisconnectedSpace (closedPoints T) := ⟨inferInstance, inferInstance, inferInstance⟩
  have : T2Space (closedPoints T) := hprof.2.1
  have : TotallyDisconnectedSpace (closedPoints T) := hprof.2.2
  refine ⟨hprof, ?_, unique_specialization_of_unique_component,
    wLocal_iff_unique_component hclosed, ?_, ?_⟩
  · intro hu
    have : WLocalSpace T := {
      eq_of_specializes := fun {x c d} hc hd hxc hxd ↦
        congrArg Subtype.val ((hu x).unique (y₁ := ⟨c, mem_closedPoints_iff.mpr hc⟩)
          (y₂ := ⟨d, mem_closedPoints_iff.mpr hd⟩) hxc hxd)
      isClosed_closedPoints := hclosed }
    let e : closedPoints T ≃ₜ ConnectedComponents T := closedPointsHomeomorph
    let r : T → closedPoints T := e.symm ∘ ConnectedComponents.mk
    have hrcont : Continuous r := e.symm.continuous.comp ConnectedComponents.continuous_coe
    have hrfix (c : closedPoints T) : r c.val = c := e.symm_apply_apply c
    have hrmk (x : T) : ConnectedComponents.mk (r x).val = ConnectedComponents.mk x :=
      e.apply_symm_apply (ConnectedComponents.mk x)
    have hrspec (x : T) : x ⤳ (r x).val := by
      obtain ⟨c, hxc, _⟩ := hu x
      have hrc : r x = c := by
        apply e.injective
        exact (hrmk x).trans hxc.connectedComponents_mk_eq
      exact hrc.symm ▸ hxc
    refine ⟨⟨r, hrcont, hrspec, hrfix, ?_⟩,
      isHomeomorph_connectedComponents_closedPoints T, e.compactSpace,
      e.t2Space, e.totallyDisconnectedSpace⟩
    intro c
    refine ⟨?_, component_eq_generalizations c⟩
    ext x
    change r x = c ↔ x ∈ connectedComponent c.val
    constructor
    · intro hrc
      exact ConnectedComponents.coe_eq_coe'.mp ((hrmk x).symm.trans (congrArg
        (fun d : closedPoints T ↦ ConnectedComponents.mk d.val) hrc))
    · intro hx
      apply e.injective
      exact (hrmk x).trans (ConnectedComponents.coe_eq_coe'.mpr hx)
  · intro R _
    constructor
    · intro hR
      have : IsWLocalRing R := hR
      exact ⟨isClosed_closedPoints, (wLocal_iff_unique_component isClosed_closedPoints).mp
        (inferInstance : WLocalSpace (PrimeSpectrum R))⟩
    · rintro ⟨hc, hu⟩
      exact ⟨(wLocal_iff_unique_component hc).mpr hu⟩
  · intro R _ _ m _
    let c : closedPoints (PrimeSpectrum R) :=
      ⟨⟨m, inferInstance⟩, mem_closedPoints_iff.mpr
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr inferInstance)⟩
    rw [component_eq_generalizations c]
    rw [PrimeSpectrum.localization_comap_range (Localization.AtPrime m) m.primeCompl]
    ext p
    change p ⤳ (⟨m, inferInstance⟩ : PrimeSpectrum R) ↔
      Disjoint (m.primeCompl : Set R) (p.asIdeal : Set R)
    rw [← PrimeSpectrum.le_iff_specializes]
    change p.asIdeal ≤ m ↔ Disjoint (m.primeCompl : Set R) (p.asIdeal : Set R)
    constructor
    · intro hp
      exact Set.disjoint_left.mpr fun a ham hap ↦ ham (hp hap)
    · intro hp a ha
      by_contra ham
      exact Set.disjoint_left.mp hp ham ha

end WLocalSpace
