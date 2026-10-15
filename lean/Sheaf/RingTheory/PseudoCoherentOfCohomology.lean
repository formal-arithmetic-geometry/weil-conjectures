/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Homology.Single
import Sheaf.CategoryTheory.TruncationTriangle
import Sheaf.RingTheory.PseudoCoherentIffAllM
import Sheaf.RingTheory.MPseudoCoherentShift
import Sheaf.RingTheory.MPseudoCoherentVanishingBase
import Sheaf.RingTheory.PseudoCoherentDistinguishedTriangle
import Sheaf.RingTheory.MPseudoCoherent

/-!
# Pseudo-coherence from pseudo-coherent cohomology

Source: Stacks Project, More on Algebra, Tag 066B, lemma-cohomology-pseudo-coherent,
pseudo-coherent clause
(blueprint: lem-weil-pbc-pseudocoherent-cohomology-implies-pseudocoherent).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A cohomologically bounded-above object whose cohomology modules, placed in degree zero,
are pseudo-coherent is pseudo-coherent.

Source: Stacks Project, More on Algebra, Tag 066B, lemma-cohomology-pseudo-coherent,
pseudo-coherent clause
(blueprint: lem-weil-pbc-pseudocoherent-cohomology-implies-pseudocoherent).

Proof: choose a representative complex C and put T_q = τ≤q C. Its cohomology equals that
of K through q and vanishes above q; hence Q(T_q) ≅ K for q ≥ b. Fix an integer m.
By lem-pc-ring-pseudo-coherent-iff-all-m, H^q(K)[0] is (m-q)-pseudo-coherent.
Iterating lem-pc-ring-m-pseudo-coherent-shift, in either direction as necessary, shows
that H^q(K)[-q] is m-pseudo-coherent. Put B = max(b,m-1). At q = m-1, T_q has zero
cohomology in every degree ≥ m, so lem-pc-ring-m-pseudo-coherent-vanishing-base applies.
Induct for q = m,...,B using lem-weil-pbc-truncation-triangle: its outer vertices are
T_(q-1) and H^q(K)[-q]. The second clause of
lem-pc-ring-pseudo-coherent-distinguished-triangle gives m-pseudo-coherence of T_q.
At B ≥ b, transport the finite-free approximation across Q(T_B) ≅ K; cohomology
functors preserve its isomorphisms and the degree-m surjection, as required by
def-pc-ring-m-pseudo-coherent. Since m was arbitrary, apply the converse of
lem-pc-ring-pseudo-coherent-iff-all-m to C to obtain a bounded-above finite-free model.
This finite induction also covers b < m, zero cohomology, and arbitrary lower tails. -/
theorem isPseudoCoherent_of_homology
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj K))
    (hcoh : ∀ i : ℤ, IsPseudoCoherent
      (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj
        ((homologyFunctor (ModuleCat.{v} R) i).obj K)))) :
    IsPseudoCoherent K := by
  sorry

end DerivedCategory
