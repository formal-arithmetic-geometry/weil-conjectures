/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.FiniteType
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.DepthLeSupportDimension
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.CohenMacaulayRingUniversallyCatenary

/-!
# Regular rings are universally catenary

Source: Stacks Project, Algebra, Tags 00NQ (lemma-regular-ring-CM) and 00NM
(lemma-CM-ring-catenary), with the definitions in Tags 00NI and 00NL
(blueprint: lem-trf-regular-ring-universally-catenary).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A Noetherian ring whose localization at every prime is regular local is universally
catenary. Source: Stacks Project, Algebra, Tags 00NQ and 00NM
(blueprint: lem-trf-regular-ring-universally-catenary).

Proof:
1. Fix a prime `p` and write `S = Localization.AtPrime p`. The hypothesis `IsRegularRing R`
   makes `S` Noetherian regular local. Its dimension `d` is finite, and its maximal ideal
   has a generating set of `d` elements. By
   `lem-weil-pbc-regular-local-generators-regular-sequence` (Tag 00NQ) these elements form
   an `S`-regular sequence. The maximal ideal is proper, so the definition of depth
   (`def-weil-pbc-depth`, using `def-weil-pbc-regular-sequence`) gives `depth S ≥ d`.
   The nonzero finite `S`-module `S` has support all of `Spec S`; its support dimension
   is therefore `d` (`def-weil-pbc-krull-dimension-ring`). Apply
   `lem-weil-pbc-depth-le-support-dimension` (Tag 00LK) to get `depth S ≤ d`.
   Thus every prime localization has depth equal to dimension. When `d = 0`, the
   regular sequence is empty and both inequalities give zero. No uniform dimension
   bound on the prime localizations of `R` is used.
2. Apply `lem-trf-cm-ring-universally-catenary` (Tag 00NM) to `R`, with its Noetherianity
   and the local Cohen--Macaulay equalities from step 1. This yields
   `IsUniversallyCatenary R` from `def-exc-excellent-ring`: every finite type `R`-algebra
   (`def-weil-pbc-finite-type-algebra`) has a finite bound on strict prime-chain lengths
   in each prime interval, and any two saturated chains in that interval have the same
   length. Saturation excludes inserting a prime between adjacent terms, and length
   counts strict inclusions. -/
theorem IsRegularRing.isUniversallyCatenary (R : Type u) [CommRing R] [IsRegularRing R] :
    IsUniversallyCatenary R := sorry
