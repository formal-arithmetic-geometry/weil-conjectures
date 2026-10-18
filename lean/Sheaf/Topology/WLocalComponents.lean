/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.Topology.SpectralClosedSubspace
import Sheaf.Topology.ProconstructibleClosureSpecialization

/-!
# Closed points and connected components of w-local spaces

Source: blueprint `sec-proetale-coefficients/sk-def-pe-wlocal/det-pe-wlocal-components.md`;
Stacks Project, Tags 0968 and 096A (blueprint: det-pe-wlocal-components).
-/

@[expose] public section

universe u v

open Topology

namespace WLocalSpace

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
2. A compact open of this subspace is retrocompact by
`lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact`, hence constructible by
`def-weil-constructible-subset`. Apply
`lem-weil-pbc-spectral-proconstructible-closure-specialization` to its one-member family.
Every point of its closure specializes from a point of that open, hence equals that point.
Thus every compact open is clopen.
3. Spectrality supplies compactness and a compact-open basis. Sobriety supplies T0.
Distinct points are separated by a basis clopen and its complement. This proves Hausdorffness
and total disconnectedness, giving the first assertion.
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
  sorry

end WLocalSpace
