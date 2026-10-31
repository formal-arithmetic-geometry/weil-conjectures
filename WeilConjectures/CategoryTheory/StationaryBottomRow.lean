/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-! # Canonical stationary comparisons along the bottom row

Source: Stacks Project, Homology, Tags 011N, 011O and 0BDV; the row-collapse
sentence in the latest blueprint cancellation proof
(blueprint: lem-weil-pbc-stationary-bottom-row).

The comparison at consecutive pages is characterized by its square with the
actual cycles inclusion and homology quotient. Since the inclusion is invertible,
this square says precisely that the comparison is its inverse followed by the
homology quotient and the specified next-page isomorphism. The comparisons `T`
identify any two late pages. The maps `a n k` identify page two with page `k+2`
at `(n,0)`; thus `a n n` reaches the stable entry on page `n+2`.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory

open Limits

/-- A spectral sequence supported in its nonnegative bottom row has canonical
stationary comparisons between late pages and from page two along the bottom row.

Source: Stacks Project, Homology, Tags 011N (spectral sequences), 011O
(degeneration and stationary pages) and 0BDV (boundedness).
(blueprint: lem-weil-pbc-stationary-bottom-row).

Proof:
1. At any page at least two, if `q ≠ 0`, the middle term is zero, so both
   adjacent differentials vanish (`def-sp-abelian`). If `q = 0`, their source
   and target have rows `r-1 > 0` and `1-r < 0`, so both vanish by support.
2. Apply `lem-weil-pbc-short-complex-zero-homology`: the cycles inclusion and
   homology quotient are isomorphisms. Compose the inverse inclusion, quotient,
   and specified page isomorphism (`def-sp-spectral-sequence`). Its inverse is
   the inverse page isomorphism, inverse quotient, and inclusion in reverse order.
   This proves the consecutive-page square below and fixes the comparison uniquely.
3. Define `T` by finite composites of these consecutive comparisons, starting
   with the identity; for the reverse direction use inverse composites. Induction
   and associativity give identity and composition for arbitrary orders of pages.
4. At `(n,0)` the same argument works on every page from page two. Starting
   with the identity, compose the consecutive comparisons to obtain `a n k`.
   Its recursion is the last cycles square below, and every `a n k` is invertible.
   Page `n+2` exceeds `max(n,1)`, so `a n n` reaches the stable bottom entry.
   When `n=0`, this is the empty composite `a 0 0`, the identity on page two.
-/
theorem spectralSequence_stationary_bottom_row
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : E₂CohomologicalSpectralSequence C)
    (hsupport : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      p < 0 ∨ q ≠ 0 → IsZero ((E.page r hr).X (p, q))) :
    (∀ (p q r : ℤ) (hr : 2 ≤ r), max p (q + 1) < r →
      (E.page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0 ∧
      IsIso ((E.page r hr).iCycles (p, q)) ∧
      IsIso ((E.page r hr).homologyπ (p, q))) ∧
    (∃ T : ∀ (p q r : ℤ) (hr : 2 ≤ r) (_hl : max p (q + 1) < r)
        (s : ℤ) (hs : 2 ≤ s) (_hsl : max p (q + 1) < s),
        (E.page r hr).X (p, q) ≅ (E.page s hs).X (p, q),
      (∀ (p q r : ℤ) (hr : 2 ≤ r) (hl : max p (q + 1) < r),
        T p q r hr hl r hr hl = Iso.refl _) ∧
      (∀ (p q r s t : ℤ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ht : 2 ≤ t)
          (hlr : max p (q + 1) < r) (hls : max p (q + 1) < s)
          (hlt : max p (q + 1) < t),
        T p q r hr hlr s hs hls ≪≫ T p q s hs hls t ht hlt =
          T p q r hr hlr t ht hlt) ∧
      (∀ (p q r : ℤ) (hr : 2 ≤ r) (hl : max p (q + 1) < r),
        (E.page r hr).iCycles (p, q) ≫
            (T p q r hr hl (r + 1) (by omega) (by omega)).hom =
          (E.page r hr).homologyπ (p, q) ≫ (E.iso r (r + 1) (p, q) rfl hr).hom)) ∧
    (∃ a : ∀ n k : ℕ,
        (E.page 2).X (n, 0) ≅ (E.page ((k : ℤ) + 2)).X (n, 0),
      (∀ n : ℕ, a n 0 = Iso.refl _) ∧
      (∀ n k : ℕ,
        (E.page ((k : ℤ) + 2)).d
            ((n : ℤ) - (k + 2), (k : ℤ) + 2 - 1) (n, 0) = 0 ∧
        (E.page ((k : ℤ) + 2)).d (n, 0)
            ((n : ℤ) + (k + 2), -((k : ℤ) + 2) + 1) = 0 ∧
        IsIso ((E.page ((k : ℤ) + 2)).iCycles (n, 0)) ∧
        IsIso ((E.page ((k : ℤ) + 2)).homologyπ (n, 0)) ∧
        (E.page ((k : ℤ) + 2)).iCycles (n, 0) ≫
            (a n k).inv ≫ (a n (k + 1)).hom =
          (E.page ((k : ℤ) + 2)).homologyπ (n, 0) ≫
            (E.iso ((k : ℤ) + 2) (((k + 1 : ℕ) : ℤ) + 2) (n, 0)).hom)) := by
  classical
  have hd (p q r : ℤ) (hr : 2 ≤ r) :
      (E.page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0 := by
    by_cases hq : q = 0
    · constructor
      · exact (hsupport r hr (p - r) (q + r - 1)
          (Or.inr (by omega))).eq_of_src _ _
      · exact (hsupport r hr (p + r) (q - r + 1)
          (Or.inr (by omega))).eq_of_tgt _ _
    · exact ⟨(hsupport r hr p q (Or.inr hq)).eq_of_tgt _ _,
        (hsupport r hr p q (Or.inr hq)).eq_of_src _ _⟩
  have hi (p q r : ℤ) (hr : 2 ≤ r) : IsIso ((E.page r hr).iCycles (p, q)) := by
    apply (E.page r hr).isIso_iCycles (p, q) (p + r, q - r + 1) _ (hd p q r hr).2
    apply ComplexShape.next_eq'
    change (p, q) + (r, 1 - r) = (p + r, q - r + 1)
    ext <;> dsimp
    all_goals omega
  have hπ (p q r : ℤ) (hr : 2 ≤ r) : IsIso ((E.page r hr).homologyπ (p, q)) := by
    apply (E.page r hr).isIso_homologyπ (p - r, q + r - 1) (p, q) _ (hd p q r hr).1
    apply ComplexShape.prev_eq'
    change (p - r, q + r - 1) + (r, 1 - r) = (p, q)
    ext <;> dsimp
    all_goals omega
  let step (p q r : ℤ) (hr : 2 ≤ r) :
      (E.page r hr).X (p, q) ≅ (E.page (r + 1)).X (p, q) :=
    (asIso ((E.page r hr).iCycles (p, q))).symm ≪≫
      asIso ((E.page r hr).homologyπ (p, q)) ≪≫ E.iso r (r + 1) (p, q)
  let A (p q : ℤ) : ∀ (r : ℤ) (hr : 2 ≤ r),
      (E.page 2).X (p, q) ≅ (E.page r hr).X (p, q) :=
    Int.leInduction (Iso.refl _) (fun r hr e ↦ e ≪≫ step p q r hr)
  have hA (p q r : ℤ) (hr : 2 ≤ r) :
      A p q (r + 1) (by omega) = A p q r hr ≪≫ step p q r hr :=
    Int.leInduction_add_one _ _ r hr
  have hA₂ (p q : ℤ) : A p q 2 (by omega) = Iso.refl _ :=
    Int.leInduction_base _ _
  have hstep (p q r : ℤ) (hr : 2 ≤ r) :
      (E.page r hr).iCycles (p, q) ≫ (step p q r hr).hom =
        (E.page r hr).homologyπ (p, q) ≫ (E.iso r (r + 1) (p, q)).hom := by
    simp [step]
  have hcompat (p q r r' : ℤ) (hr : 2 ≤ r) (hrr' : r + 1 = r') :
      (E.page r hr).iCycles (p, q) ≫ (A p q r hr).inv ≫
          (A p q r' (by omega)).hom =
        (E.page r hr).homologyπ (p, q) ≫ (E.iso r r' (p, q) hrr' hr).hom := by
    subst r'
    rw [hA]
    simpa using hstep p q r hr
  refine ⟨fun p q r hr _ ↦ ⟨(hd p q r hr).1, (hd p q r hr).2,
    hi p q r hr, hπ p q r hr⟩, ?_, ?_⟩
  · refine ⟨fun p q r hr _ s hs _ ↦ (A p q r hr).symm ≪≫ A p q s hs, ?_, ?_, ?_⟩
    · intro p q r hr hl
      ext
      simp
    · intro p q r s t hr hs ht hlr hls hlt
      ext
      simp
    · intro p q r hr hl
      dsimp only
      rw [hA]
      simpa using hstep p q r hr
  · refine ⟨fun n k ↦ A n 0 ((k : ℤ) + 2) (by omega), ?_, ?_⟩
    · intro n
      exact hA₂ n 0
    · intro n k
      refine ⟨?_, ?_,
        hi n 0 ((k : ℤ) + 2) (by omega), hπ n 0 ((k : ℤ) + 2) (by omega), ?_⟩
      · exact (hsupport ((k : ℤ) + 2) (by omega)
          ((n : ℤ) - (k + 2)) ((k : ℤ) + 2 - 1)
          (Or.inr (by omega))).eq_of_src _ _
      · exact (hsupport ((k : ℤ) + 2) (by omega)
          ((n : ℤ) + (k + 2)) (-((k : ℤ) + 2) + 1)
          (Or.inr (by omega))).eq_of_tgt _ _
      · exact hcompat n 0 ((k : ℤ) + 2) (((k + 1 : ℕ) : ℤ) + 2)
          (by omega) (by omega)

end CategoryTheory
