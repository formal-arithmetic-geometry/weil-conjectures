/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DeltaFunctor
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Exact comparison detected on an embedding class

Source: blueprint, `sec-six-functors/sk-lem-sf-kunneth-star`, proof,
"Field coefficients and sheaves", kernel calculation and induction on degree
(blueprint: lem-sf-exact-delta-embedding-detection).
-/

@[expose] public section

universe vC vB uC uB

namespace CategoryTheory

/-- A degreewise natural comparison from exact additive functors to a cohomological
 delta-functor is invertible everywhere if each object embeds into an object where all
 comparison components are invertible. No compatibility with connecting morphisms is required.

Source: blueprint, `sec-six-functors/sk-lem-sf-kunneth-star`, proof,
"Field coefficients and sheaves", final kernel-and-induction paragraphs
(blueprint: lem-sf-exact-delta-embedding-detection).

Proof:
1. Complete the stipulated mono `i : Q ⟶ P` by its cokernel `p : P ⟶ Q'` to a short
   exact sequence, using `lem-weil-pbc-abelian-exact-epi-cokernel`. Exactness of every
   `F r` makes its image short exact, so `(F r).map i` is mono and `(F r).map p` is epi.
2. Naturality identifies `(a r).app Q ≫ (G.F r).map i` with
   `(F r).map i ≫ (a r).app P`, which is mono. Cancellation shows every `(a r).app Q`
   is mono, simultaneously for all objects and degrees, including `Q'`.
3. In degree zero, pad the image rows `Q ⟶ P ⟶ Q'` by two zero objects. They are
   exact at their three interior objects: for `F` by short exactness, and for `G` by
   its initial monicity and middle exactness. The five vertical maps are the two
   zero-object identities and the comparisons at `Q`, `P`, `Q'`. The first is epi,
   the second and fourth are iso, and the fifth is mono. Apply
   `lem-weil-pbc-five-lemma` to obtain invertibility at `Q` in degree zero.
4. Induct on degree, with the assertion quantified over all objects. The preceding
   degree's comparison is invertible at both `P` and `Q'`. Naturality for `p` and
   epimorphy of its `F` image imply epimorphy of its `G` image. Its composite with
   the connecting map is zero, so the connecting map vanishes. Exactness then makes
   the next `G` image of `i` mono; middle exactness already holds.
5. Apply the same padded five lemma in this degree. The comparison at `P` is iso by
   its choice and that at `Q'` is mono by step 2. This completes the induction.
   All comparison squares use only naturality within a single degree. -/
theorem exactDeltaComparison_isIso_of_embeddings
    {C : Type uC} {B : Type uB} [Category.{vC} C] [Abelian C]
    [Category.{vB} B] [Abelian B]
    (F : ℕ → C ⥤ B) [∀ r : ℕ, (F r).Additive]
    (hF : ∀ (r : ℕ) (S : ShortComplex C), S.ShortExact → (S.map (F r)).ShortExact)
    (G : CohomologicalDeltaFunctor C B) (a : ∀ r : ℕ, F r ⟶ G.F r)
    (hembed : ∀ Q : C, ∃ (P : C) (i : Q ⟶ P),
      Mono i ∧ ∀ r : ℕ, IsIso ((a r).app P)) :
    ∀ (Q : C) (r : ℕ), IsIso ((a r).app Q) := by
  have hmono (Q : C) (r : ℕ) : Mono ((a r).app Q) := by
    obtain ⟨P, i, hi, hP⟩ := hembed Q
    let S := ShortComplex.cokernelSequence i
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact i
        mono_f := hi }
    have : Mono ((F r).map i) := (hF r S hS).mono_f
    have := hP r
    exact mono_of_mono_fac ((a r).naturality i).symm
  -- The kernel form of the five lemma handles the comparison in a single degree.
  have step (r : ℕ)
      (hG : ∀ (S : ShortComplex C), S.ShortExact → Mono ((G.F r).map S.f))
      (Q : C) : IsIso ((a r).app Q) := by
    obtain ⟨P, i, hi, hP⟩ := hembed Q
    let S := ShortComplex.cokernelSequence i
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact i
        mono_f := hi }
    have hFS := hF r S hS
    obtain ⟨w, hw⟩ := G.exact_middle S hS r
    let φ : ComposableArrows.mk₂ ((F r).map S.f) ((F r).map S.g) ⟶
        ComposableArrows.mk₂ ((G.F r).map S.f) ((G.F r).map S.g) :=
      ComposableArrows.homMk₂ ((a r).app S.X₁) ((a r).app S.X₂)
        ((a r).app S.X₃) ((a r).naturality S.f) ((a r).naturality S.g)
    refine Abelian.isIso_of_isIso_of_mono φ hFS.exact.exact_toComposableArrows
      hw.exact_toComposableArrows ?_ ?_ ?_ ?_
    · change Mono ((F r).map S.f)
      exact hFS.mono_f
    · change Mono ((G.F r).map S.f)
      exact hG S hS
    · change IsIso ((a r).app S.X₂)
      exact hP r
    · change Mono ((a r).app S.X₃)
      exact hmono S.X₃ r
  suffices ∀ r Q, IsIso ((a r).app Q) from fun Q r ↦ this r Q
  intro r
  induction r with
  | zero => exact step 0 (fun S hS ↦ G.mono_zero S hS)
  | succ r ih =>
    apply step (r + 1)
    intro S hS
    have : Epi ((F r).map S.g) := (hF r S hS).epi_g
    have := ih S.X₃
    have : Epi ((G.F r).map S.g) :=
      epi_of_epi_fac ((a r).naturality S.g).symm
    obtain ⟨w, _⟩ := G.exact_right S hS r
    have hδ : G.delta S hS r = 0 := by
      apply (cancel_epi ((G.F r).map S.g)).1
      simpa only [Limits.comp_zero] using w
    obtain ⟨w', hw'⟩ := G.exact_left S hS r
    exact hw'.mono_g hδ

end CategoryTheory
