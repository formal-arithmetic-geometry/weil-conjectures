/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Codegree polygon cost and minimum

Source: Morrison, *GIT Constructions of Moduli Spaces of Stable Curves and Maps*,
Section 2.4, Lemma 6 and Figure 2, pp. 11--12.
(blueprint: def-sfb-codegree-polygon)
-/

@[expose] public section

open scoped BigOperators

namespace Gieseker

/-- Cost of the increasing subsequence obtained by sorting `s`, summed over
successive pairs. Source: Morrison, Section 2.4, Lemma 6
(blueprint: def-sfb-codegree-polygon). -/
noncomputable def codegreePolygonCost {N : ℕ} (e : Fin N → ℤ) (w : Fin N → ℝ)
    (s : Finset (Fin N)) : ℝ :=
  (((s.sort (· ≤ ·)).zip (s.sort (· ≤ ·)).tail).map
    (fun p => ((e p.1 : ℝ) + (e p.2 : ℝ)) * (w p.1 - w p.2))).sum

/-- Infimum of polygon costs over finite subsequences containing both endpoints.
For positive `N`, this finite nonempty family has the intended minimum.
Source: Morrison, Section 2.4, Lemma 6
(blueprint: def-sfb-codegree-polygon). -/
noncomputable def codegreePolygonMinimum {N : ℕ} (e : Fin N → ℤ) (w : Fin N → ℝ) : ℝ :=
  sInf {b : ℝ | ∃ s : Finset (Fin N),
    (∃ i ∈ s, i.val = 0) ∧ (∃ i ∈ s, i.val + 1 = N) ∧
      b = codegreePolygonCost e w s}

end Gieseker
