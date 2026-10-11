/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# A bounded-size criterion for K-injectivity

Source: Stacks Project, `injectives.tex`, Lemma `lemma-characterize-K-injective`
(blueprint: lem-pur-kinjective-characterize-K-injective).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Source: Stacks Project, `injectives.tex`, Lemma `lemma-characterize-K-injective`
(blueprint: lem-pur-kinjective-characterize-K-injective).
The size of an object is the cardinality of its subobject set, shrunk to the hom universe
using well-poweredness of a Grothendieck category. Assume (a) nonzero acyclic complexes
contain nonzero bounded-above acyclic subcomplexes of termwise size at most `κ`, and
(b) every acyclic complex is a quotient of a coproduct of such small complexes.
Then a termwise injective complex receiving only null-homotopic maps from these small
complexes is K-injective.

Proof: Given an acyclic complex `M`, form a transfinite filtration starting at zero.
At a successor stage apply (a) to the nonzero quotient by the preceding stage and take
the inverse image. At a limit take the filtered colimit, which remains acyclic by exactness
of filtered colimits (`def-sp-grothendieck-abelian`). The filtration eventually reaches `M`
since each term has a set of subobjects.
Inductively prove vanishing of homotopy-category Hom from every shift of every stage to `I`.
At successors use the short exact sequence with small bounded-above acyclic quotient,
`lem-pur-kinjective-homotopy-exact-injective-target`, termwise injectivity
(`def-sp-injective-resolutions`), and the small-complex hypothesis, also for shifts.
At limits the Hom complexes form a continuous inverse system with surjective transition
maps by termwise injectivity; apply `lem-pur-kinjective-homotopy-limit-vanishing` and the
inductive vanishing for all shifts. At the terminal stage specialize to shift zero.
Every map from the arbitrary acyclic `M` to `I` is then null-homotopic, which is precisely
K-injectivity (`def-pur-kinjective-complex`). -/
theorem isKInjective_of_small_acyclic
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (κ : Cardinal.{v})
    (h_sub : ∀ (M : CochainComplex C ℤ), M.Acyclic → ¬ IsZero M →
      ∃ (N : CochainComplex C ℤ) (ι : N ⟶ M),
        Mono ι ∧ ¬ IsZero N ∧ (∃ b : ℤ, N.IsStrictlyLE b) ∧ N.Acyclic ∧
          ∀ n : ℤ, Cardinal.mk (Shrink.{v} (Subobject (N.X n))) ≤ κ)
    (h_quot : ∀ (M : CochainComplex C ℤ), M.Acyclic →
      ∃ (α : Type v) (F : α → CochainComplex C ℤ) (π : ∐ F ⟶ M),
        Epi π ∧ ∀ a : α, (∃ b : ℤ, (F a).IsStrictlyLE b) ∧ (F a).Acyclic ∧
          ∀ n : ℤ, Cardinal.mk (Shrink.{v} (Subobject ((F a).X n))) ≤ κ)
    (I : CochainComplex C ℤ)
    (h_inj : ∀ j : ℤ, Injective (I.X j))
    (h_small : ∀ (M : CochainComplex C ℤ),
      (∃ b : ℤ, M.IsStrictlyLE b) → M.Acyclic →
      (∀ n : ℤ, Cardinal.mk (Shrink.{v} (Subobject (M.X n))) ≤ κ) →
      ∀ f : M ⟶ I, Nonempty (Homotopy f 0)) :
    I.IsKInjective := by
  sorry

end CochainComplex
