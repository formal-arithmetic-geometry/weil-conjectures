/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.ProEtale.WContractible

import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.HenselianFactorizationCriterion
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.RingTheory.HenselianPairPrimeConnected
import Sheaf.Topology.WLocalComponents
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import WeilConjectures.RingTheory.FactorsThroughLocalization
import Sheaf.RingTheory.WLocalClopenPartitions
import Mathlib.RingTheory.Smooth.Basic
import Sheaf.RingTheory.HenselianSmoothAlgebraLifting
import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian

/-!
# Henselian reduction and w-strict locality

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 2.2.13, with the
local-ring characterization in Lemma 2.2.9
(blueprint: lem-zl-henselian-wstrict-local-invariance).
-/

@[expose] public section

universe u

/-- Henselian reduction preserves and reflects w-strict locality.
Source: Bhatt--Scholze, Lemmas 2.2.13, 2.2.9 and 2.2.15
(blueprint: lem-zl-henselian-wstrict-local-invariance).

Proof plan:
1. The henselian factorization criterion puts `I` in the Jacobson radical. The prime-spectrum
   quotient correspondence identifies `Spec (A/I)` with `V(I)` and identifies their closed
   points with those of `Spec A` (lem-weil-pbc-henselian-factorization-criterion,
   def-weil-affine-spectrum).
2. Closedness of the closed-point set and uniqueness of closed specializations descend to
   this closed subspace, giving w-locality of the quotient (sk-def-pe-wlocal).
3. Localizing the quotient at a maximal ideal gives the corresponding quotient of the
   maximal localization. Strict henselianity descends to this proper quotient, giving
   w-strict locality of `A/I` (lem-weil-pbc-localization-at-prime-of-quotient,
   lem-weil-pbc-strictly-henselian-quotient, sk-def-pe-wlocal).
4. Conversely assume `A/I` is w-strictly local. Its closed points are closed also in
   `Spec A`. For every prime `p`, the nonempty connected subset `V(p+I)` maps under the
   closed-point retraction to a singleton in the profinite closed-point space. Its maximal
   ideals are fixed by this retraction, so `p` has a unique maximal specialization. Thus
   `A` is w-local (lem-weil-pbc-henselian-pair-prime-connected, det-pe-wlocal-components,
   sk-def-pe-wlocal).
5. For any faithfully flat etale `A`-algebra `B`, base change gives an etale surjection
   `Spec (B/IB)` to `Spec (A/I)`, using the affine tensor-product identification
   (lem-weil-pbc-faithfully-flat-surjective-spectrum, lem-weil-pbc-etale-covering-base-change,
   lem-weil-pbc-fibre-product-affine-spectra).
6. At each maximal localization of `A/I`, strict henselianity supplies a section of this
   etale surjection, hence an algebra map to that localization
   (lem-weil-pbc-etale-covering-base-change,
   lem-sbc-strict-henselian-etale-neighbourhood-section, sk-def-pe-wlocal,
   def-weil-affine-spectrum).
7. Finite presentation spreads each section to a principal open neighbourhood
   (lem-weil-pbc-etale-ring-map-iff-etale-affine,
   lem-factors-through-localization-of-smooth, def-weil-affine-spectrum).
8. Compactness and profiniteness give a subordinate finite clopen partition of the closed
   points. Extend it to `Spec (A/I)` and glue the sections on disjoint parts to an
   `A/I`-algebra map `B/IB` to `A/I` (lem-weil-pbc-w-local-partition,
   def-weil-affine-spectrum, det-pe-wlocal-components).
9. Etale implies smooth: the cotangent module and first cotangent homology vanish.
   Henselian smooth-algebra lifting lifts the resulting map `B` to `A/I` to an
   `A`-algebra map `B` to `A`, hence a retraction of the structure map
   (lem-weil-pbc-etale-ring-map-iff-etale-affine, def-weil-pbc-smooth-ring-map,
   lem-trf-henselian-smooth-algebra-lifting; Stacks Tag 0H74).
10. Every faithfully flat etale `A`-algebra therefore splits. The maximal-local criterion
    gives strictly henselian maximal localizations. Combined with step 4 this proves
    w-strict locality of `A` (lem-weil-pbc-split-etale-covers-maximal-local-criterion,
    sk-def-pe-wlocal; Stacks Tag 097V). -/
theorem isWStrictlyLocalRing_iff_quotient_of_henselianRing
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I] :
    IsWStrictlyLocalRing A ↔ IsWStrictlyLocalRing (A ⧸ I) := by
  sorry
