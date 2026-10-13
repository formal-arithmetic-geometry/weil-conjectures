/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.RingTheory.KoszulDualComplex

/-!
# Signed complementary Koszul equivalences

Source: Stacks Project, Tag 0BQZ, proof of lemma-regular-immersion-ext,
complementary contraction on the ordered top wedge.
(blueprint: lem-sc-koszul-complementary-equivalences).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- The signed complementary-wedge equivalences commute with the Koszul differentials.
No regularity is assumed.
Source: Stacks Project, Tag 0BQZ, proof of lemma-regular-immersion-ext, the map
sending a dual contraction monomial to its value on the ordered top wedge.
(blueprint: lem-sc-koszul-complementary-equivalences).

Proof: Let E = A^r with ordered basis e_i and top wedge w. For 0 <= j <= r,
let P_j(x,y) be the coefficient of w in x wedge y, with x in wedge^j E and
y in wedge^(r-j) E. The finite exterior-power bases show that P_j is perfect:
the dual of e_S maps to sign(S,S-complement) times e_(S-complement). Call
this isomorphism T'_j. Contraction d is a graded derivation. For x of degree
j+1 and y of degree r-j, x wedge y vanishes in degree r+1, so
P_j(d x,y) = (-1)^j P_(j+1)(x,d y). The signed dual differential is
delta_j(phi) = (-1)^(j+1) phi composed with d. Consequently
T'_(j+1) delta_j = -d T'_j. Set T_j = (-1)^j T'_j; then
T_(j+1) delta_j = d T_j. Multiplication by the unit (-1)^j preserves
invertibility. These T_j give e and the displayed differential identity,
with natural-number subtraction justified by j < r. When r = 0 the only
map is Hom_A(A,A) to A by evaluation at 1 and there are no differential
identities to check. Over the zero ring every term is zero and the same
basis construction and signs apply. -/
theorem exists_koszul_complementary_equivalences
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) :
    ∃ e : ∀ (j : ℕ), j ≤ r →
        (koszulDualComplex A r f).X j ≃ₗ[A] (koszulComplex A r f).X (r - j),
      ∀ (j : ℕ) (hj : j < r) (x : (koszulDualComplex A r f).X j),
        e (j + 1) (by omega) ((koszulDualComplex A r f).d j (j + 1) x) =
          (koszulComplex A r f).d (r - j) (r - (j + 1))
            (e j (Nat.le_of_lt hj) x) := by sorry

end ExteriorAlgebra
