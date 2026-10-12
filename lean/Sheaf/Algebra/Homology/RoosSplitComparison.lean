/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism
import Sheaf.Algebra.Homology.KernelShiftedMappingCone

/-! # Roos comparison for complexes with split transitions

Source: Stacks Project, Derived Categories, Tag 070M, and the split-envelope
extension recorded in lem-weil-derived-limit-roos-complex.
(blueprint: lem-weil-roos-split-comparison).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A split-term complex has a product/kernel/signed-cone presentation whose
canonical comparison is a quasi-isomorphism. This is the split case, with no
K-injectivity hypothesis.

Proof: Form PJ termwise by countable products and let sJ be one minus transition
shift. Naturality of the transition shift gives a chain map. Define LJ as its
kernel complex. Define CJ explicitly with terms PJ^(p-1) ⊞ PJ^p and differential
(y,x) ↦ (-dy-sJ x, dx); the square is zero by commutation of d and sJ.
Choose a section σ_n of each split transition in every degree. On the product
recursively define a_n by a_0=0 and a_(n+1)=(a_n-pr_n)σ_n. Their product lift a
satisfies a sJ = id by checking every projection, so sJ is degreewise epi.
Apply the degreewise-epi kernel/shifted-cone comparison, and transport it through
the explicit identification of the signed cone with the shifted Mathlib cone.
Its projection equations identify it with (0,iJ) and give the asserted equations.
The kernel comparison is a quasi-isomorphism, and conjugating by the cone
isomorphism preserves this property.

Source: Stacks Project, Derived Categories, Tag 070M; the agent-written extension
in lem-weil-derived-limit-roos-complex.
(blueprint: lem-weil-roos-split-comparison). -/
theorem roos_split_comparison
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A]
    (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hSplit : ∀ (p : ℤ) (n : ℕ),
      IsSplitEpi ((J.X p).map (homOfLE (Nat.le_succ n)).op)) :
    ∃ (PJ LJ CJ : CochainComplex A ℤ)
      (ePJ : ∀ p : ℤ, PJ.X p ≅ ∏ᶜ (fun n : ℕ ↦ (J.X p).obj (Opposite.op n)))
      (sJ : PJ ⟶ PJ) (iJ : LJ ⟶ PJ)
      (hKJ : ∀ p : ℤ, iJ.f p ≫ sJ.f p = 0)
      (eCJ : ∀ p : ℤ, CJ.X (p + 1) ≅ PJ.X p ⊞ PJ.X (p + 1))
      (etaJ : LJ ⟶ CJ)
      (_hLJ : ∀ p : ℤ, IsLimit (KernelFork.ofι (iJ.f p) (hKJ p))),
      (∀ p q : ℤ, PJ.d p q ≫ (ePJ q).hom =
      (ePJ p).hom ≫ Limits.Pi.map (fun n ↦ (J.d p q).app (Opposite.op n))) ∧
      (∀ p : ℤ, sJ.f p = (ePJ p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (J.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (ePJ p).inv) ∧
      (∀ p : ℤ, CJ.d (p + 1) (p + 1 + 1) ≫ (eCJ (p + 1)).hom =
      (eCJ p).hom ≫ biprod.lift
        (-(biprod.fst ≫ PJ.d p (p + 1)) - biprod.snd ≫ sJ.f (p + 1))
        (biprod.snd ≫ PJ.d (p + 1) (p + 1 + 1))) ∧
      (∀ p : ℤ, etaJ.f (p + 1) ≫ (eCJ p).hom = biprod.lift 0 (iJ.f (p + 1))) ∧
      QuasiIso etaJ := by
  sorry

end CategoryTheory
