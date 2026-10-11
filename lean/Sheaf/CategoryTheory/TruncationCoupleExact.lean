/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.CategoryTheory.TruncationCouple
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exactness of the truncation couple

Source: Weil conjectures blueprint, sec-proper-base-change, sk-thm-properbasechange,
node lem-sp-truncation-couple-exact, order 1210; Stacks Project, Tags 08J5, 05SE,
0148 and 011Q (blueprint: lem-sp-truncation-couple-exact).
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The truncation couple `truncationCouple F K a ha` = (D, E, alpha, f, g) is an exact
couple: at each of its three kinds of vertex the two consecutive structure maps compose
to zero and the resulting short complex is exact. The vertices are D^{p+2,q-1} (incoming
f : E^{p,q} → D^{p+2,q-1}, outgoing alpha), E^{p,q} (incoming g : D^{p,q} → E^{p,q},
outgoing f) and D^{p-1,q+1} (incoming alpha : D^{p,q} → D^{p-1,q+1}, outgoing g); since
p and q range over all of ℤ these are the three kernel = image conditions of
def-sp-exact-couple at every bidegree.

Proof (the four steps of the node):
1. By `lem-weil-pbc-truncation-triangle`, form the canonical triangle T_q with terms
   tau_{<=q-1}K, tau_{<=q}K and H^q(K)[-q]. All three are bounded below.
   `lem-sp-grothendieck-enough-injectives` supplies enough injectives, so the right
   derived functor exists by `lem-weil-pbc-derived-direct-image-triangulated`.
   `def-sp-kinjective-bridge` and `lem-sp-kinjective-computes` identify its cohomology
   with the chosen-resolution terms of `def-sp-truncation-couple`. The inclusions
   from T_{q+1} induce alpha, the projections from T_q induce g, and the third maps
   of T_q followed by the derived shift isomorphism induce f. Their bidegrees are
   (-1,+1), (0,0) and (+2,-1), respectively. The lower vanishing bound is unused.
2. `lem-weil-pbc-derived-direct-image-triangulated` sends each T_q to a distinguished
   triangle in D^+(B), hence in D(B).
3. By `lem-sf-derived-homology-long-exact`, its long exact cohomology sequence contains
   D^{p+1,q-1} -> D^{p,q} -> E^{p,q} -> D^{p+2,q-1} -> D^{p+1,q},
   with maps alpha, g, f, alpha. The connecting map is cohomology of the third arrow
   followed by H^n(M[1]) = H^{n+1}(M), exactly the boundary defining f.
4. Exactness for T_q gives ker g = im alpha and ker f = im g at (p,q).
   Exactness for T_{q+1}, in total degree p+q, gives ker alpha = im f at D^{p,q},
   with incoming term E^{p-2,q+1}. These equalities also give all three zero
   composites. Since p and q are arbitrary, these are all the conditions required by
   `def-sp-exact-couple`.

Source: Weil conjectures blueprint, sec-proper-base-change, sk-thm-properbasechange,
node lem-sp-truncation-couple-exact, order 1210; Stacks Project, Derived Categories,
Remark 08J5, Proposition 05SE and sequence 0148; Homological Algebra, Definition 011Q
(blueprint: lem-sp-truncation-couple-exact). -/
theorem truncationCouple_exact
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q)) :
    (∀ p q : ℤ,
      ∃ w : (truncationCouple F K a ha).2.2.2.1 p q ≫
          (truncationCouple F K a ha).2.2.1 (p + 2) (q - 1) = 0,
        (ShortComplex.mk _ _ w).Exact) ∧
    (∀ p q : ℤ,
      ∃ w : (truncationCouple F K a ha).2.2.2.2 p q ≫
          (truncationCouple F K a ha).2.2.2.1 p q = 0,
        (ShortComplex.mk _ _ w).Exact) ∧
    (∀ p q : ℤ,
      ∃ w : (truncationCouple F K a ha).2.2.1 p q ≫
          (truncationCouple F K a ha).2.2.2.2 (p - 1) (q + 1) = 0,
        (ShortComplex.mk _ _ w).Exact) := by
  sorry

end CategoryTheory
