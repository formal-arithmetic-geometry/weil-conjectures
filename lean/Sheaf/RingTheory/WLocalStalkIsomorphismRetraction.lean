/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.ExtremallyDisconnected
import Sheaf.RingTheory.ProfiniteComponentRingPullback
import Sheaf.RingTheory.WLocalClosedComponentRetraction

/-!
# Retractions of w-local maps identifying local rings

Source: Stacks Project, Tag 09AZ, `lemma-w-local-extremally-disconnected`,
proof of (3) implies (1)
(blueprint: lem-weil-pbc-wlocal-stalk-isomorphism-retraction).
-/

@[expose] public section

universe u v

namespace RingHom

/-- Stacks Project, Tag 09AZ, proof of (3) implies (1)
(blueprint: lem-weil-pbc-wlocal-stalk-isomorphism-retraction).
A faithfully flat map identifying all local rings has a retraction when its source
and target are w-local, its source component space is extremally disconnected, and
the closed-point loci are defined by an ideal and its extension.

Proof: faithful flatness makes the spectrum map surjective, hence also the induced
continuous map on connected components. The component spaces are compact Hausdorff
by `lem-weil-pbc-profinite-component-ring-pullback`. Projectivity of the extremally
disconnected target (`lem-weil-pbc-extremally-disconnected-component-section`)
gives a continuous section. Its image is closed and maps bijectively to the source
component space. The two zero-locus equalities show that closed points contract to
closed points. Apply `lem-weil-pbc-wlocal-closed-component-retraction` to this image,
using the assumed bijectivity of every canonical localization map, to obtain the
ring retraction. Spectrum surjectivity is
`lem-weil-pbc-faithfully-flat-surjective-spectrum`. -/
theorem exists_retraction_of_wLocal_stalk_isomorphisms
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : g.FaithfullyFlat) [IsWLocalRing R] [IsWLocalRing S]
    [ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))]
    (I : Ideal R)
    (hI : PrimeSpectrum.zeroLocus (I : Set R) = closedPoints (PrimeSpectrum R))
    (hIS : PrimeSpectrum.zeroLocus (I.map g : Set S) = closedPoints (PrimeSpectrum S))
    (hlocal : ∀ (q : Ideal S) [q.IsPrime],
      Function.Bijective (Localization.localRingHom (q.comap g) q g rfl)) :
    ∃ s : S →+* R, s.comp g = RingHom.id R := by
  sorry

end RingHom
