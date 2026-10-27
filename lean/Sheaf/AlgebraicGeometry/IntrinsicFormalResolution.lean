/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.ElkikTowerComparison
import WeilConjectures.RingTheory.RegularBaseChange
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Intrinsic regular functoriality of completed resolution towers

Source: Temkin, Non-embedded Desingularization, Proposition 3.3.5, Lemma 3.3.3,
§§3.3.4--3.3.8 and 3.4.1 (blueprint: lem-per-rig-formal-resolution-intrinsic).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Elkik

/-- Regular morphisms of sufficiently thick Elkik fibres compare the ordered centered
towers at every common precision, compatibly under restriction. Regular maps of completed
pairs compare the completed towers; over a fixed identification of completions this
comparison is unique. `Pair` includes finite disjoint unions with possibly different fields,
and the rule is applied to the whole scheme, retaining synchronization of its stages.

Source: Temkin Proposition 3.3.5, §§3.3.4--3.3.8 and 3.4.1
(blueprint: lem-per-rig-formal-resolution-intrinsic).

Proof plan:
1. The uniform smooth-span lifting lemma (lem-per-elkik-smooth-span-lifting) gives an
etale span inducing a smooth thick map, with the etale leg an isomorphism at every order.
Regular functoriality identifies the two ordinary pullbacks; no supported source center
vanishes under that leg. Restrict to a common precision.
2. Use the rational smooth model systems (lem-per-elkik-rational-smooth-models), fix a
target stage, and factor the regular thick map through a smooth map on a neighborhood
of the closed fibre of a later source stage. The uniform target conductor gives r.
3. Fix the two model towers. Each center contains a power of the distinguished ideal.
The finite sum of these exponents bounds the precision loss, by the chart calculation
of lem-per-supported-blowup-precision-loss. Compare spans and source stages after common
refinement; the same estimate gives agreement on overlaps, hence gluing.
4. For M=n² and sufficiently large n>P, n(n-P)≤M-L. Comparisons therefore restrict
compatibly at every allowed t. If P=0 the comparison is just the cartesian base map and
there is no precision loss. Delete empty centers only at common precision.
5. Reduce a regular completed map modulo every ideal power. Regular finite-type base
change (lem-weil-pbc-regular-base-change) and the canonical completion quotient identities
(lem-weil-pbc-adic-completion-mod-power) give regular thick maps. The preceding estimate
makes their comparisons compatible across n; all supported center ideals stabilize.
6. Pass to the inverse-limit structure sheaves. The inverse finite-level comparisons
give formal isomorphisms onto the contracted pullback. Over a fixed completion, center
ratios topologically generate each completed blowup chart, so the comparison is unique.
An identification and its inverse give inverse tower identifications. No uniqueness of
arbitrary truncated-tower automorphisms is asserted.
7. For finite disjoint unions use the rule on the whole union, take the maximum of
component thresholds and the sum of center bounds, and delete a stage exactly when all
its component centers are empty. This preserves their synchronization and order. -/
theorem intrinsic_formal_resolution :
    (∀ X : Pair.{u}, ∃ r : ℕ,
      ∀ F : (S : Scheme.{u}) → OrdinaryBlowupTower S, IsStrongRegularRule F →
      ∀ Y : Pair.{u}, ∃ N : ℕ,
        max (F X.scheme).length (F Y.scheme).length < N ∧
        ∀ n : ℕ, N ≤ n →
          ∀ h : Y.fibre (n ^ 2 + r) ⟶ X.fibre (n ^ 2 + r),
            IsRegularSchemeMorphism h →
            (X.fibreIdeal (n ^ 2 + r)).comap h = Y.fibreIdeal (n ^ 2 + r) →
            Nonempty (FiniteComparison (F X.scheme) (F Y.scheme) (n ^ 2 + r)
              (n * (n - max (F X.scheme).length (F Y.scheme).length)) h)) ∧
    (∀ F : (S : Scheme.{u}) → OrdinaryBlowupTower S, IsStrongRegularRule F →
      ∀ (X Y : Pair.{u}) (h : CompletedMap X Y), h.IsRegular →
        Nonempty (CompletedComparison (F X.scheme) (F Y.scheme) h)) ∧
    (∀ F : (S : Scheme.{u}) → OrdinaryBlowupTower S, IsStrongRegularRule F →
      ∀ (X Y : Pair.{u}) (e : CompletedIso X Y),
        Nonempty (CompletedComparison (F X.scheme) (F Y.scheme) e.toMap) ∧
        Subsingleton (CompletedComparison (F X.scheme) (F Y.scheme) e.toMap)) := by
  sorry

end AlgebraicGeometry.Elkik
