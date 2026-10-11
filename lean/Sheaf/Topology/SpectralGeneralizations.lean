/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Spectral.Basic

/-!
# Generalizations of quasi-compact subsets in spectral spaces

Source: Stacks Project, Topology, Lemma 0A31 (label `lemma-make-spectral-space`, line 5005),
implication (3) => (4) and the quasi-compactness of `W`.
(blueprint: lem-weil-pbc-spectral-generalizations-of-quasi-compact)
-/

@[expose] public section

universe u

open Set Topology

namespace Topology

/-- In a spectral space, the generalizations of a quasi-compact set are quasi-compact and
are the intersection of all quasi-compact opens containing that set.

Source: Stacks Project, Topology, Lemma 0A31 (`lemma-make-spectral-space`), proof of
(3) => (4), third paragraph. Write `W` for the displayed generalization set.

1. Reflexivity of specialization gives `E ⊆ W`. If an open `U` contains `E` and
   `w ∈ W`, choose `e ∈ closure {w} ∩ E`. The open neighbourhood `U` of `e` meets
   `{w}`, so `w ∈ U`. Thus every open containing `E` contains `W`.
2. Given an open cover of `W`, compactness of `E` supplies a finite subfamily
   covering `E`. Its open union contains `W` by step 1, proving compactness of `W`.
3. For `x ∉ W`, the closed set `Z = closure {x}` misses `W`: if `w ∈ Z ∩ W`,
   then `closure {w} ⊆ Z`, and its intersection with `E` would imply `x ∈ W`.
4. By the compact-open basis in `def-weil-spectral-space`, every point of `W`
   has a compact open neighbourhood inside `X ∖ Z`. Step 2 supplies finitely many
   covering `W`. Their union is compact and open, contains `E`, and excludes `x`.
5. Step 1 places `W` inside every compact open containing `E`; step 4 excludes
   every point outside `W` from their intersection. This proves the equality.
   This family contains `X`, which is compact and open by `def-weil-spectral-space`.
   Step 2 gives the first conjunct.

(blueprint: lem-weil-pbc-spectral-generalizations-of-quasi-compact) -/
theorem generalizations_isCompact_sInter_isCompactOpen
    (X : Type u) [TopologicalSpace X] [SpectralSpace X]
    (E : Set X) (hE : IsCompact E) :
    IsCompact {x : X | closure ({x} : Set X) ∩ E ≠ ∅} ∧
      {x : X | closure ({x} : Set X) ∩ E ≠ ∅} =
        ⋂₀ {U : Set X | IsOpen U ∧ IsCompact U ∧ E ⊆ U} := by
  sorry

end Topology
