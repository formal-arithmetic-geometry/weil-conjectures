/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.RingTheory.IsMittagLeffler
import Sheaf.RingTheory.Flat.LazardPresentation
import Sheaf.SecTraceFormula.MLCountableColimit
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Sequential finite-free presentation of a countably generated flat Mittag-Leffler module

Source: Stacks Project, Algebra, Tags 059X and 059W and the paragraph after 059W.
(blueprint: lem-trf-countable-flat-ml-sequential-presentation)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Module

/-- A countably generated flat Mittag-Leffler module has a sequential finite-free
presentation. Lean index `n : ℕ` denotes the paper's stage `n + 1`. The successive
transition is `G.map (homOfLE (Nat.le_succ n))`; naturality of `ι` states compatibility
with its maps to `P`. No injectivity condition is imposed on the transitions.

Source: Stacks Project, Algebra, Tag 059X (lemma-countgen-projective), opening paragraph;
Tag 059W (lemma-ML-countable-colimit) and the following cofinal-sequence paragraph.
(blueprint: lem-trf-countable-flat-ml-sequential-presentation)

Proof:
1. By lem-weil-pbc-flat-tensor-exact, flatness gives exactness and preservation of
   injections after tensoring with P. By lem-weil-pbc-tensor-right-exact, surjections
   are also preserved. Apply lem-kun-lazard-flat-module to obtain a small nonempty
   directed partial order I, finite-free stages F_i, and a colimit cocone with vertex P.
2. Each finite-free stage is finitely presented: use the zero map R^0 -> R^r and
   transport its cokernel presentation across the finite-free equivalence. Apply
   lem-trf-ml-countable-colimit using the Mittag-Leffler and countable-generation
   hypotheses. It supplies a nonempty countable directed subset J of I whose
   restricted cocone is still a colimit, by def-weil-pbc-category-colimit.
3. Enumerate J as b_1, b_2, ... with repetitions if finite. Set j_1 = b_1 and choose
   j_(n+1) above j_n and b_(n+1) in J. Then every i in J lies below some j_n.
   Restrict the stages, transitions, ranks and cocone maps to this sequence.
   Finite-freeness and compatibility are inherited; no strict increase is needed.
4. To verify the sequential colimit by def-weil-pbc-category-colimit, take any compatible
   maps h_n : F_(j_n) -> N. For i in J choose n with i <= j_n and define h_i as h_n
   composed with F_(i,j_n). For two choices n,m choose l >= n,m; sequential
   compatibility makes both expressions equal to h_l composed with F_(i,j_l).
   Thus the maps are independent of the choice and form a cocone on J. The colimit
   property on J gives a unique map P -> N restricting to all h_i, hence all h_n.
   Conversely, a map restricting to every h_n restricts to every h_i by the same
   formula, so uniqueness on J gives sequential uniqueness. -/
theorem exists_sequential_finite_free_presentation_of_flat_isMittagLeffler
    (R : Type u) [CommRing R] (P : Type (max u v)) [AddCommGroup P] [Module R P]
    [Module.Flat R P]
    (hML : Module.IsMittagLeffler.{u, max u v, max u v, 0} R P)
    (hcountable : ∃ E : Set P, E.Countable ∧ Submodule.span R E = ⊤) :
    ∃ (G : ℕ ⥤ ModuleCat.{max u v} R)
      (ι : G ⟶ (Functor.const ℕ).obj (ModuleCat.of R P)) (r : ℕ → ℕ),
      (∀ n : ℕ, Nonempty ((G.obj n) ≃ₗ[R] (Fin (r n) → R))) ∧
        Nonempty (IsColimit (Cocone.mk (ModuleCat.of R P) ι)) := by
  sorry

end Module
