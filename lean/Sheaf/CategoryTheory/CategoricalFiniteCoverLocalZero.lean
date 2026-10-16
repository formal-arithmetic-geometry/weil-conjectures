/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! # Locally zero generalized sections of a presheaf with zero sheafification

Source: Stacks Project, Tags 00W1 and 00WB, expressed using exact filtered
colimits of local restriction kernels rather than underlying elements.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  (J : GrothendieckTopology C) [HasSheafify J A]
  [∀ V : C, HasFiniteProducts (Over V)]

/-- A map from a presheaf with zero sheafification vanishes if it vanishes on
all generalized sections killed by restriction to a finite basis cover.
Source: Stacks Project, Section 7.10 (Tag 00W1), the filtered-colimit equality
description before Lemma 7.10.8 and Theorem 7.10.10 (Tag 00WB), extended using
AB5 to Grothendieck abelian coefficients.
(blueprint: stage3-categorical-finite-cover-local-zero).

Proof: For each covering sieve R on V, take the kernel K_R of the restriction
map from P(V) to the matching-family object over R. Refinement gives an increasing
filtered family of subobjects. The kernel of P(V) → P⁺(V) is their filtered union:
compute P⁺(V) as the filtered colimit of matching-family objects and use AB5.
Each R has the stipulated finite refinement U, and K_R is contained in the kernel
of the finite product of restrictions to U. This finite product can equivalently
be indexed by the one-fold nerve terms, using their canonical singleton-product
isomorphisms. Thus b kills the kernel of the plus unit. Before applying hcov
to covering members, replace the cover by its one-fold nerve cover: its members
have B literally, with no isomorphism-invariance assumption on B.

Iterate this assertion through the transfinite plus construction. At a successor
stage, pull back the local restriction kernels along the earlier unit. For each
of the finitely many covering members the induction hypothesis expresses the
pulled-back kernel as a filtered union of kernels of further finite restrictions.
Exact filtered colimits commute with these finite pullbacks and products. Compose
the resulting finite covers and refine again using hcov. At each recursive step
use the one-fold nerve cover so that its members satisfy B. Consequently every pulled-back
kernel remains a filtered union of kernels killed by a single finite basis
cover (the cover may vary with the subobject). At a limit stage AB5 identifies
the kernel with the union of the earlier kernels. The same argument applies to
the colimit of all stages. For a sufficiently large regular cardinal that
colimit is a sheafification; hence the kernel of the original unit is all of
P(V), because the given sheafification is zero. The restrictions of b to this
jointly epimorphic family of locally zero subobjects vanish by h, so b is zero.
Empty covers contribute the entire P(V), since their product is zero, and the
argument includes V covered by the empty sieve. No choice of a uniform cover
for all of P(V), and no projective generator of A, is assumed. -/
theorem hom_eq_zero_of_sheafification_zero
    (B : C → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
      (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (P : Cᵒᵖ ⥤ A) (hP : IsZero ((presheafToSheaf J A).obj P))
    (V : C) (hV : B V) {T : A} (b : P.obj (op V) ⟶ T)
    (h : ∀ {n : ℕ} (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
      ∀ {E : A} (x : E ⟶ P.obj (op V)),
        x ≫ cechAugmentation U Over.mkIdTerminal ((Over.forget V).op ⋙ P) = 0 →
        x ≫ b = 0) : b = 0 := by
  sorry

end CategoryTheory.Presheaf
