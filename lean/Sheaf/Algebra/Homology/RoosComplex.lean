/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism

/-! # Roos complexes for inverse limits

Source: Stacks Project, derived.tex, Tag 070M (lemma-difficulty-K-injectives),
extended to arbitrary K-injective towers by the node's split-envelope argument
(blueprint: lem-weil-derived-limit-roos-complex).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The canonical Roos comparison is a quasi-isomorphism. The isomorphisms `eP` and `eC`
identify the product and shifted cone terms; their differential equations specify the
complexes, and the kernel and comparison equations specify the canonical map.
Source: Stacks Project, derived.tex, Tag 070M (lemma-difficulty-K-injectives)
(blueprint: lem-weil-derived-limit-roos-complex).

Proof: (1) The kernel of the transition endomorphism is the inverse limit, naturally in
families (tower-transition-endomorphism and inverse-system definitions). (2) Applying
products and limits termwise preserves homotopies; on the cone use the homotopy
`(-P(h)y, P(h)x)`. (3) On split towers recursively choose a section of `1-s`
(lem-weil-tower-split-envelope), so it is split epi. (4) For complexes with split terms,
the degreewise-epi kernel/cone comparison is a quasi-isomorphism
(lem-weil-degreewise-epi-kernel-cocone-qis). (5) Embed the tower complex in its additive
split envelope and use the cokernel's shifted cone to replace it by a quasi-isomorphic
complex with split terms (lem-weil-tower-category-levelwise-abelian and
lem-weil-tower-split-envelope). (6) K-injectivity gives a homotopy retraction of this
replacement (lem-weil-pbc-kinjective-hom-derived). (7) Naturality and homotopy invariance
make the comparison a retract of the split-term comparison on every cohomology object;
thus it is a quasi-isomorphism and its derived-category image is an isomorphism. -/
theorem roosComplex_quasiIso
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A] [HasExactLimitsOfShape (Discrete ℕ) A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    (P L C : CochainComplex A ℤ)
    (eP : ∀ p : ℤ, P.X p ≅ ∏ᶜ (fun n : ℕ ↦ (I.X p).obj (Opposite.op n)))
    (hP : ∀ p q : ℤ, P.d p q ≫ (eP q).hom =
      (eP p).hom ≫ Limits.Pi.map (fun n ↦ (I.d p q).app (Opposite.op n)))
    (oneSubS : P ⟶ P)
    (hS : ∀ p : ℤ, oneSubS.f p = (eP p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (eP p).inv)
    (iota : L ⟶ P)
    (hKernel : ∀ p : ℤ, iota.f p ≫ oneSubS.f p = 0)
    (hL : ∀ p : ℤ, IsLimit (KernelFork.ofι (iota.f p) (hKernel p)))
    (eC : ∀ p : ℤ, C.X (p + 1) ≅ P.X p ⊞ P.X (p + 1))
    (hC : ∀ p : ℤ, C.d (p + 1) (p + 1 + 1) ≫ (eC (p + 1)).hom =
      (eC p).hom ≫ biprod.lift
        (-(biprod.fst ≫ P.d p (p + 1)) - biprod.snd ≫ oneSubS.f (p + 1))
        (biprod.snd ≫ P.d (p + 1) (p + 1 + 1)))
    : ∃ eta : L ⟶ C,
      (∀ p : ℤ, eta.f (p + 1) ≫ (eC p).hom = biprod.lift 0 (iota.f (p + 1))) ∧
      QuasiIso eta ∧ IsIso ((DerivedCategory.Q).map eta) := by
  sorry

end CategoryTheory
