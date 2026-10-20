/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!
# The ordinary associated graded of a flat convolution

Source: Stacks Project, More on Algebra, Section `section-kunneth-spectral-sequence`,
paragraphs preceding Tag 0H7W (blueprint: lem-kun-flat-convolution-graded-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex

variable {R : Type u} [CommRing R]

local instance : HasColimitsOfSize.{0, 0} (ModuleCat.{u} R) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

/-- The ordinary convolution quotient is the sum of the tensor products of graded pieces.
The filtration `G` and its maps from step tensors are specified by their actual image
and inclusion equations, so no choice of a comparison map enters the hypotheses.

Source: Stacks, More on Algebra, Section `section-kunneth-spectral-sequence`,
the short exact sequence and its kernel calculation before Tag 0H7W
(blueprint: lem-kun-flat-convolution-graded-iso).

Proof: finite induction on the graded layers shows that the quotients of each underlying
term by a filtration step are flat. For each pair `(i,j)` on the diagonal `i+j=a`, project
the tensor to `(P/F^(i+1)) tensor (Q/F^(j+1))`. On a step tensor on that diagonal every
component except its own vanishes: at another index one factor is in the next step.
Flat quotient tensor injectivity identifies its diagonal image with `gr^i P tensor gr^j Q`.
Right exactness of tensor identifies its kernel with the sum of tensors in which either
factor is in its next step. The restricted maps therefore give a surjection from `G^a`
to the diagonal sum, with kernel exactly `G^(a+1)`: express an element of `G^a` as a finite
sum of step tensors, and use the off-diagonal vanishing to test the kernel separately
on every summand. All maps commute with the signed tensor differential. The cokernel
universal property gives the inverse of the asserted isomorphism. Lifting both residue
classes to step representatives proves the displayed equation. There is no boundedness
condition on cochain degrees, and zero filtrations and empty nonzero diagonals give the
same argument with zero objects. -/
theorem flatConvolution_graded_iso
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ))
    (hPfin : P.filtration.IsFinite) (hQfin : Q.filtration.IsFinite)
    (hP : ∀ n, ObjectProperty.flat (P.obj.X n))
    (hQ : ∀ n, ObjectProperty.flat (Q.obj.X n))
    (hPs : ∀ i n, ObjectProperty.flat
      ((P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X n))
    (hQs : ∀ i n, ObjectProperty.flat
      ((Q.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X n))
    (hPg : ∀ i n, ObjectProperty.flat ((P.filtration.gradedPiece i).X n))
    (hQg : ∀ i n, ObjectProperty.flat ((Q.filtration.gradedPiece i).X n))
    (G : DecreasingFiltration (P.obj ⊗ Q.obj))
    (hG : ∀ a : ℤ, G.step a = imageSubobject
      (Sigma.desc (fun i : ℤ ↦
        (P.filtration.step i).arrow ⊗ₘ (Q.filtration.step (a - i)).arrow)))
    (l : ∀ a i : ℤ,
      (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) ⊗
          (Q.filtration.step (a - i) : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
        (G.step a : CochainComplex (ModuleCat.{u} R) ℤ))
    (hl : ∀ a i, l a i ≫ (G.step a).arrow =
      (P.filtration.step i).arrow ⊗ₘ (Q.filtration.step (a - i)).arrow) :
    ∀ a : ℤ, ∃ e :
      (∐ fun i : ℤ ↦ P.filtration.gradedPiece i ⊗ Q.filtration.gradedPiece (a - i)) ≅
        G.gradedPiece a,
      ∀ i : ℤ,
        (P.filtration.complexQuotientπ i (i + 1) (by omega) ⊗ₘ
          Q.filtration.complexQuotientπ (a - i) (a - i + 1) (by omega)) ≫
          Sigma.ι (fun i : ℤ ↦
            P.filtration.gradedPiece i ⊗ Q.filtration.gradedPiece (a - i)) i ≫ e.hom =
        l a i ≫ G.complexQuotientπ a (a + 1) (by omega) := by
  sorry

end CochainComplex
