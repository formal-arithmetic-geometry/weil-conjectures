/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

import Sheaf.Paper.ContinuousRingUniverseRealization
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Invariant rank of finite free continuous coefficient sheaves

Source: Hemo--Richarz--Scholbach, Example 3.1, p. 6; blueprint
`sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice-rank.proof.md`,
first paragraph (blueprint: lem-sfb-continuous-coefficient-free-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Finite free continuous coefficient sheaves on a nonempty scheme have invariant rank.
The normed algebra structure specifies the unique extension of the ℓ-adic norm to `E`.
The finite biproduct defining `Mod.finiteFree` includes the zero module in rank zero.

Source: Hemo--Richarz--Scholbach, Example 3.1, p. 6; blueprint stratified-lattice rank
proof, first paragraph (blueprint: lem-sfb-continuous-coefficient-free-rank).

Proof:
1. The unique extended absolute value is nonarchimedean
   (`lem-weil-l-adic-extension-absolute-value`). Ultrametric balls are clopen and separate
   distinct points, so `E` is totally disconnected. Apply
   `lem-sfb-continuous-ring-universe-realization` to identify the coefficient ring object
   with the ring sheaf `R(U) = C(|U|, E)`. Transport the given isomorphism and its inverse
   along this ring isomorphism, retaining both inverse identities.
2. For each finite biproduct use its inclusions `i_j` and projections `p_j`.
   They satisfy `p_j i_k = δ_jk` and `Σ i_j p_j = 1`, including the empty sum in rank zero
   (`sk-def-sfb-module-objects`, `def-weil-additive-category`).
3. A regular-module endomorphism `h` satisfies `h_W(a) = a h_W(1)` by its module-morphism
   equation. For the transported maps `f` and `g`, take entries
   `A_ij = (p_i f i_j)_W(1)` and `B_ji = (p_j g i_i)_W(1)` in `C(|W|, E)`.
   Insert the biproduct identity resolutions into `gf = 1` and `fg = 1`.
   Linearity on sections and commutativity give `BA = I_m` and `AB = I_n`.
4. Choose `w : W`. Evaluation at `w` preserves all ring operations, so the evaluated
   matrices define mutually inverse linear maps `E^m` and `E^n`. The same formulas use
   empty matrices and empty sums when either rank is zero.
5. The standard coordinate vectors are bases of these spaces, of dimensions `m` and `n`
   (`def-weil-vector-space-dimension`). Their images under the two inverse maps are
   independent. Apply `lem-weil-independent-family-card-le-dimension` in both directions
   to obtain `m ≤ n` and `n ≤ m`, and conclude by antisymmetry. -/
theorem continuous_coefficient_finiteFree_rank
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (W : Scheme.{u}) [Nonempty W] (m n : ℕ)
    (_e : Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) W) m ≅
      Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) W) n) :
    m = n := by
  sorry

end AlgebraicGeometry.ProEtale
