/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks

import Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Finiteness of the n-fold relative Frobenius

Source: Stacks Project, Varieties, Tags 0CCD and 0CCG
(blueprint: lem-trf-relative-frobenius-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- For a locally finite type morphism to a characteristic-`p` scheme, the n-fold
relative Frobenius is finite.

Source: Stacks Project, Varieties, Tags 0CCD and 0CCG
(blueprint: lem-trf-relative-frobenius-finite).

Proof, following the five DAG steps:

1. Set `Y_i = X ×_{S,F_S^i} S`, with projections `π_i` and `s_i`, and identify
   `Y_0` with `X`. Pulling back `p = 0` along `s_i` gives its characteristic
   [def-weil-scheme-characteristic-p]. For `Z_i = Y_i ×_{S,F_S} S`, the pair
   `(π_i a_i,b_i)` defines `θ_i : Z_i ⟶ Y_(i+1)`. Conversely the pair
   `(π_(i+1), F_S s_(i+1))` defines `c_i : Y_(i+1) ⟶ Y_i`, and
   `(c_i,s_(i+1))` defines its inverse `η_i`. Checking both projections proves
   `θ_i η_i = id` and `η_i θ_i = id` [def-pc-fibre-product]. Naturality of
   Frobenius gives the one-step map `u_i : Y_i ⟶ Z_i`; put `r_i = θ_i u_i`.
   Its projections are `π_i F_(Y_i)` and `s_i`
   [def-weil-absolute-frobenius-scheme].
2. Each `u_i` is integral by [lem-trf-relative-frobenius-universal-homeomorphism].
   Its composite with `θ_i` remains integral: on an affine target open, pull back
   by the isomorphism and transport each monic equation's coefficients through
   the section-ring isomorphism [def-weil-finite-integral-morphism]. Starting
   with `C_1 = r_0`, integral composition, clause (e) of
   [lem-weil-pbc-closed-immersion-integral-separated-uc], makes
   `C_i = r_(i-1) ... r_0` integral for every positive `i`.
3. Inductively the projections of `C_i` are `F_X^i` and `f`. The induction uses
   Frobenius naturality `π_i F_(Y_i) = F_X π_i`, which on sections is preservation
   of p-th powers [def-weil-absolute-frobenius-scheme]. Uniqueness in
   [def-pc-fibre-product] identifies `C_n` with the specified n-fold map.
4. Its composite with the second projection is `f`, locally of finite type by
   assumption. Clause (f) of [lem-weil-pbc-proper-fp-permanence] makes this map
   locally of finite type, without any condition on the second projection.
5. Apply the reverse implication of [lem-weil-pbc-finite-iff-integral-lft] to
   its integrality from steps 2 and 3 and its local finite type from step 4.
-/
theorem relativeFrobenius_finite
    (p : ℕ) (S X : Scheme.{u}) (hS : S.IsCharacteristic p) (f : X ⟶ S)
    [LocallyOfFiniteType f] (n : ℕ) (hn : 1 ≤ n) :
    ∃ hX : X.IsCharacteristic p,
      ∃ r : X ⟶ pullback f (S.iterateFrobenius hS.1 (hS.2 ⊤) n),
        r ≫ pullback.fst f (S.iterateFrobenius hS.1 (hS.2 ⊤) n) =
            X.iterateFrobenius hX.1 (hX.2 ⊤) n ∧
        r ≫ pullback.snd f (S.iterateFrobenius hS.1 (hS.2 ⊤) n) = f ∧
        IsFinite r ∧
        ∀ s : X ⟶ pullback f (S.iterateFrobenius hS.1 (hS.2 ⊤) n),
          s ≫ pullback.fst f (S.iterateFrobenius hS.1 (hS.2 ⊤) n) =
              X.iterateFrobenius hX.1 (hX.2 ⊤) n →
          s ≫ pullback.snd f (S.iterateFrobenius hS.1 (hS.2 ⊤) n) = f →
          s = r := by
  sorry

end AlgebraicGeometry.Scheme
