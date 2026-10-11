/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.RingTheory.NagataRing

/-!
# Nagata rings are universally Japanese

Source: Stacks Project, Algebra, Proposition 10.162.4 (Tag 0334), implication
(1) ⇒ (3) (blueprint: lem-weil-pbc-nagata-universally-japanese).
-/

universe u

/-- A Nagata ring is universally Japanese: every finite type domain algebra is N-2.

Source: Stacks Project, Algebra, Proposition 10.162.4 (Tag 0334), implication
(1) ⇒ (3) (blueprint: lem-weil-pbc-nagata-universally-japanese).

Proof, following the six steps of the node:
1. For a monogenic extension of domains `A ⊆ B = A[x]` with `A` Nagata, write
   `K = Frac(A)` and `L = Frac(B)`. If `x` is transcendental over `K`, evaluation
   identifies `B` with `A[X]`. The zero prime shows `A` is N-2, and
   `lem-weil-pbc-polynomial-ring-n2` (Tag 032O) shows `B` is N-2.
2. If `x` is algebraic, `L = K(x)` is finite over `K` by
   `lem-weil-pbc-algebraic-generators-finite-extension`. For any finite `M/L`,
   `lem-weil-pbc-finite-module-over-finite-algebra` makes `M/K` finite. The integral
   closure `A'` of `A` in `M` is finite over `A` by N-2. It is normal with fraction
   field `M` by `lem-weil-pbc-integral-closure-finite-extension-normal`, and Nagata
   by `lem-weil-pbc-finite-over-nagata-nagata` (Tag 032T).
3. Put `T = A'[x]` inside `M`. Finite `A`-module generators of `A'` generate `T`
   over `B`, and `Frac(T) = M`. Since `T` is integral over `B`, the integral closure
   `B'` of `B` in `M` equals that of `T`: one inclusion uses the same monic
   equations, the other `lem-weil-pbc-integral-transitive`.
4. By `lem-weil-pbc-normal-nagata-monogenic-n1`, `T` is N-1, so `B'` is finite
   over `T`, and hence over `B` by `lem-weil-pbc-finite-module-over-finite-algebra`.
   This proves N-2 for every monogenic extension of Nagata domains.
5. For any monogenic algebra `A → B` over a Nagata ring, `B` is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`. For a prime `q` of `B`, let `p`
   be its inverse image. The domain `A/p` is Nagata by
   `lem-weil-pbc-finite-over-nagata-nagata`. The induced monogenic domain extension
   `A/p ⊆ B/q` is N-2 by steps 1-4, proving that `B` is Nagata.
6. Factor a finite type map into finitely many monogenic maps and apply step 5
   inductively. Thus every finite type `R`-algebra `S` is Nagata. If `S` is a
   domain, its zero prime quotient is `S` itself, so it is N-2. This is precisely
   `IsUniversallyJapanese R`, as defined in Tag 032R.
-/
theorem isUniversallyJapanese_of_isNagataRing (R : Type u) [CommRing R]
    (hR : IsNagataRing R) : IsUniversallyJapanese R := by
  sorry
