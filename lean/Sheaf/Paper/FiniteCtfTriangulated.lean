/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Finite-stage constructible complexes of finite Tor amplitude

Source: Stacks Project, Cohomology on Sites, Tag 08G2, lemma-cone-tor-amplitude (2),
and the Weil blueprint, finite-stage paragraph of `def-weil-finite-tor-amplitude`
(blueprint: lem-weil-finite-ctf-triangulated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

/-- Bounded constructibility and finite Tor amplitude cut out a strictly full triangulated
subcategory on the small pro-etale site. The last two clauses retain the precise interval
bounds under shifts and extensions.

Source: Stacks Project, Cohomology on Sites, Tag 08G2, lemma-cone-tor-amplitude (2),
Tag 08FZ, definition-tor-amplitude; Weil blueprint, finite-stage paragraph of
`def-weil-finite-tor-amplitude` (blueprint: lem-weil-finite-ctf-triangulated).

Proof plan:
1. The coefficient-extension valuation ring is a DVR with finite residue field; apply
`lem-weil-valued-dvr-finite-quotients` at the positive level. Then
`lem-weil-proetale-dbc-triangulated` gives all bounded-constructibility closure clauses.
2. The exact-derived-tensor clause of `lem-weil-pbc-ringed-projection-mate-exact`, applied
on the identity ringed topos, says tensor with each degree-zero module preserves shifts
and distinguished triangles. Use the constant ring and small site of
`def-weil-proetale-tor-amplitude`, without changing coefficient or site encodings.
3. Tensor and cohomology preserve isomorphisms, so vanishing outside an interval is
isomorphism invariant. Additivity sends zero to zero, giving zero amplitude `[0,0]`.
4. Cohomological shifts give H^i(C[m]) = H^(i+m)(C), hence the bound `[a-m,b-m]`.
Shifting back by `-m` gives the converse for finite amplitude and constructibility.
5. Enlarge two endpoint intervals to their common minimum/maximum interval. For every
module sheaf, tensor the distinguished triangle and apply
`lem-sf-derived-homology-long-exact`: outside that interval both endpoint cohomologies
vanish, so the middle cohomology vanishes. A preassigned common interval is unchanged.
6. Conjoin the bounded-constructibility and finite-amplitude closure properties and
apply `def-weil-triangulated-subcategory`. Strict fullness supplies isomorphism closure;
zero, all integer shifts, and middle vertices give the inherited triangulated structure.
-/
theorem finite_ctf_isTriangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E n hn Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K) ∧
    ObjectProperty.IsTriangulated
      (intrinsicFiniteTorsionConstructible l E n hn Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K) ∧
    (∀ (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) (a b m : ℤ),
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
        (K⟦m⟧) (a - m) (b - m)) ∧
    (∀ (T : Triangle (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)))
      (a b : ℤ), T ∈ distTriang _ →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₁ a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₃ a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₂ a b) := by
  sorry

end AlgebraicGeometry.Scheme
