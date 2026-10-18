/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.RingTheory.FiniteProjectiveK0

/-!
# The K₀ class of a finite projective module with a finite free resolution

Source: literature/stacks-project/more-algebra.tex, Tag 0AFY
(blueprint: lem-trf-invertible-module-k0-class).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u v

open Module

namespace Module.FiniteProjectiveK0

/--
A finite free resolution gives the alternating sum of the classes of its free terms.
The family `M` encodes the displayed sequence: `M 0` is `L`, and `M (i.succ)` is
`F_i`; the map indexed by `i` goes from the term at `i.succ` to the term at `i`.
The hypotheses `hsurj` and `hinj` express exactness at the two endpoints, while
`hexact` expresses exactness at every interior term.  The basis hypothesis records
that `F_i` has a basis with `r i` elements.

Source: Stacks Project, More on Algebra, Tag 0AFY (more-algebra-lemma-perfect-to-K-group),
clauses (2) and (3), lines 36491--36558
(blueprint: lem-trf-invertible-module-k0-class).

Proof:
1. Let the successive syzygies be the images and kernels in the given exact
   sequence. Exactness produces short exact sequences between consecutive
   syzygies, with the leftmost map an isomorphism.
2. Starting with the finitely generated projective module `L`, split each short
   exact sequence using the projective lifting property. Each next syzygy is a
   finitely generated projective direct summand of a finite free module. This
   uses `def-weil-pbc-projective-module`, `def-weil-pbc-free-module`,
   `def-weil-finitely-generated-module`, and `def-weil-pbc-exact-sequence`.
3. In `def-trf-k0-group`, split sequences give `[F_i] = [K_(i+1)] + [K_i]`
   (and `[F_d] = [K_d]`), so the alternating sum telescopes to `[L]`.
4. A basis of `r_i` elements identifies `F_i` with `S^(r_i)`. The direct-sum
   relation in `def-trf-k0-group` therefore gives `[F_i] = r_i [S]`, yielding
   the displayed alternating sum and hence the final existential assertion.
-/
theorem class_of_finite_free_resolution
    (S : Type u) [CommRing S]
    (d : ℕ) (r : Fin (d + 1) → ℕ)
    (M : Fin (d + 2) → Type v)
    [hAdd : ∀ i, AddCommGroup (M i)] [hMod : ∀ i, Module S (M i)]
    [Module.Finite S (M 0)] [Module.Projective S (M 0)]
    (h : ∀ i : Fin (d + 1),
      M i.succ →ₗ[S] M i.castSucc)
    (hfree : ∀ i : Fin (d + 1),
      Nonempty (Basis (Fin (r i)) S (M i.succ)))
    (hexact : ∀ i : Fin d,
      Function.Exact (h i.succ) (h i.castSucc))
    (hsurj : Function.Surjective (h 0))
    (hinj : Function.Injective (h (Fin.last d))) :
    mk S (M 0) =
        (∑ i : Fin (d + 1), (-1 : ℤ) ^ (i : ℕ) * (r i : ℤ)) • mk S S ∧
      ∃ n : ℤ, mk S (M 0) = n • mk S S := by
  sorry

end Module.FiniteProjectiveK0
