/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.RetainedLocalization
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
import Sheaf.RingTheory.RetainedLocalizationProperties
import Sheaf.RingTheory.WLocalStalkIsomorphismRetraction
import Sheaf.RingTheory.WeakEtaleRefinementProperties
import Sheaf.RingTheory.WeaklyEtaleField
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing

/-! # Geometric sufficient criterion for splitting weakly etale covers

Source: Stacks Project, Tag 0982, implication (3) to (1)
(blueprint: lem-weil-pbc-wcontractible-geometric-criterion).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A w-local ring with extremally disconnected connected-component space and strictly
henselian localizations at every maximal ideal splits every faithfully flat weakly etale map.
Source: Stacks Project, Tag 0982, implication (3) to (1)
(blueprint: lem-weil-pbc-wcontractible-geometric-criterion).

Proof plan:
1. Apply thm-weil-pbc-weak-etale-refinement to factor through an ind-etale R-algebra E,
   faithfully flat over B. Faithful flatness composes, and ind-etale maps are weakly etale
   by lem-weil-pbc-ind-etale-stability. A retraction after any further extension suffices.
2. Let I be the intersection of maximal ideals of R. W-locality gives V(I) equal to the
   closed points. For T = V(IE), every q in T is maximal: its contraction is maximal,
   and lem-weil-pbc-weak-etale-field makes the corresponding residue extension algebraic.
   Apply def-weil-pbc-retained-localization and lem-weil-pbc-retained-localization to form
   S = E_[T]. Then S is w-local, its closed points are precisely V(IS), and R to S is
   ind-etale, hence weakly etale by lem-weil-pbc-ind-etale-stability.
3. At a maximal ideal n of S, its contraction m is maximal in R. The canonical local map
   R_m to S_n is weakly etale by localization, base change and composition. The hypothesis
   at m and thm-weil-pbc-weak-etale-strict-local make it an isomorphism. Localizing further
   at primes below n identifies every local ring by the canonical map of
   def-weil-pbc-localization-at-prime.
4. The map R to S is flat. For p in Spec R choose a maximal m above it and, using
   lem-weil-pbc-faithfully-flat-surjective-spectrum, a prime of E over m. Its retained
   point in S lies over m. The local isomorphism lifts p to S. Thus the spectrum map is
   surjective, and lem-weil-pbc-flat-surjective-spectrum-faithfully-flat gives faithful
   flatness. When R is zero, B, E and S are zero and their spectra are empty.
5. Apply lem-weil-pbc-wlocal-stalk-isomorphism-retraction with the ideal I, w-locality,
   extremal disconnectedness, faithful flatness and the local isomorphisms. Compose the
   resulting S to R retraction with B to E to S; associativity gives r.comp f = id.
-/
theorem exists_retraction_of_wlocal_geometric_criterion
    {R : Type u} [CommRing R] [IsWLocalRing R]
    [ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))]
    (hstrict : ∀ (m : Ideal R) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m))
    {B : Type v} [CommRing B] (f : R →+* B)
    (hfaithful : f.FaithfullyFlat) (hweak : f.WeaklyEtale) :
    ∃ r : B →+* R, r.comp f = RingHom.id R := by
  sorry

end RingHom
