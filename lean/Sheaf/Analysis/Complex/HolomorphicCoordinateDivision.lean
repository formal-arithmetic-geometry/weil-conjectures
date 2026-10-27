/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Filter.Germ.Basic

/-! # Holomorphic coordinate division with parameters

Source: Serre, GAGA, §1 no. 1, printed p. 3, for holomorphic germs;
the supporting coordinate-division argument is agent-formulated
(blueprint: lem-sfb-holomorphic-coordinate-division).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Topology

namespace Complex

/-- A holomorphic germ minus its restriction to the coordinate slice `z = 0` is a sum
of the normal coordinates times holomorphic germs, with joint holomorphic dependence
on the parameters. Holomorphicity of a germ means that it has a representative with
a convergent complex power series at the origin. Composition with `(z,t) ↦ (0,t)`
is restriction to the slice followed by pullback along projection to `t`.

Source: Serre, GAGA, §1 no. 1, printed p. 3, for the notion of holomorphic germ;
agent-formulated analytic Hadamard lemma supporting §2 no. 6, Proposition 4
(blueprint: lem-sfb-holomorphic-coordinate-division).

Proof plan:
1. If `r = 0`, the slice map is the identity and the sum is empty. Otherwise choose
   a representative and a polydisc where its power series converges absolutely.
   Shrink to a common positive coordinate radius `rho`.
2. Restriction to `z = 0` retains precisely the terms with zero normal multi-index.
   Subtracting removes these terms, leaving the absolutely convergent subseries
   with nonzero normal multi-index `alpha`.
3. Assign each such monomial to the least `j` with `alpha j > 0`, and divide it by
   `z j`. For `0 < s < rho`, the sum of the absolute coefficient bounds for this
   divided series on the closed `s`-polydisc is bounded by `s⁻¹` times the original
   convergent majorant. A further shrink gives uniform absolute convergence, so
   each divided series represents a jointly holomorphic germ.
4. Multiplication by `z j` recovers each assigned monomial. The assignments partition
   the nonzero normal multi-indices, and absolute convergence allows regrouping
   to give the identity of germs. No parameter indices occur when `d = 0`. -/
theorem exists_holomorphic_coordinate_division (r d : ℕ)
    (H : Filter.Germ (𝓝 (0 : (Fin r → ℂ) × (Fin d → ℂ))) ℂ)
    (hH : ∃ f : ((Fin r → ℂ) × (Fin d → ℂ)) → ℂ,
      AnalyticAt ℂ f 0 ∧ Filter.Germ.ofFun f = H) :
    ∃ Hs : Fin r → Filter.Germ (𝓝 (0 : (Fin r → ℂ) × (Fin d → ℂ))) ℂ,
      (∀ j : Fin r, ∃ f : ((Fin r → ℂ) × (Fin d → ℂ)) → ℂ,
        AnalyticAt ℂ f 0 ∧ Filter.Germ.ofFun f = Hs j) ∧
      H - H.compTendsto (fun p : (Fin r → ℂ) × (Fin d → ℂ) ↦ (0, p.2))
        ((continuous_const.prodMk continuous_snd).tendsto 0) =
        ∑ j : Fin r,
          Filter.Germ.ofFun (fun p : (Fin r → ℂ) × (Fin d → ℂ) ↦ p.1 j) * Hs j := by
  sorry

end Complex
