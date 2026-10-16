/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.Homotopy
import all Sheaf.CategoryTheory.DoubleComplexTotal

/-! Factorization of a componentwise lower-vertical-degree homotopy through the
second filtration. (blueprint: lem-sp-cartan-eilenberg-double-complex-homotopy-filtration)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A homotopy with the displayed horizontal and vertical components lowers the
second filtration by at most one.
Source: Stacks Project, Tag 015K, with the second-filtration finite-sum formula.
(blueprint: lem-sp-cartan-eilenberg-double-complex-homotopy-filtration)

Proof:
Fix q and n and let Q be the (q-1)-st second-filtration step of J' in degree n-1.
The q-th step of I' in degree n is the finite supremum, over q <= i <= n, of the
images of the diagonal inclusions of I' at (n-i,i). By hcomp, the composite of
such an inclusion with H is the sum of its s1 component landing in vertical
degree i and its signed s2 component landing in vertical degree i-1.
Both vertical degrees are at least q-1.

For any target inclusion at (a,b) of total degree n-1 with b >= q-1, if b <= n-1
its image occurs in the finite supremum defining Q, so the inclusion factors
through Q. If b > n-1, then a < 0 and hJ makes its source zero; this inclusion
also factors through Q. Consequently both component composites factor through Q.
Factorization is preserved by integer scalar multiplication and addition, so
hcomp gives a factorization for every source diagonal inclusion followed by H.

Pull Q back along H.hom n (n-1). Each generating image of the source filtration
lies in that pullback, hence their finite supremum does too, including when the
index interval is empty. The pullback factorization equivalence therefore makes
the source filtration arrow followed by H factor through Q. Taking factorThru
and its defining equality supplies the required f and equation.
-/
theorem cartanEilenberg_secondFiltration_factor
    (C : Type u) [Category.{v} C] [Abelian C]
    (I' J' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [I'.HasTotal (ComplexShape.up ℤ)] [J'.HasTotal (ComplexShape.up ℤ)]
    (δ : I' ⟶ J')
    (hJ : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((J'.X p).X q))
    (H : Homotopy (HomologicalComplex₂.total.map δ (ComplexShape.up ℤ)) 0)
    (s1 : ∀ p q : ℤ, (I'.X p).X q ⟶ (J'.X (p - 1)).X q)
    (s2 : ∀ p q : ℤ, (I'.X p).X q ⟶ (J'.X p).X (q - 1))
    (hcomp : ∀ (p q n : ℤ) (hpq : p + q = n),
      I'.ιTotal (ComplexShape.up ℤ) p q n hpq ≫ H.hom n (n - 1) =
        s1 p q ≫ J'.ιTotalOrZero (ComplexShape.up ℤ) (p - 1) q (n - 1) +
          p.negOnePow •
            (s2 p q ≫ J'.ιTotalOrZero (ComplexShape.up ℤ) p (q - 1) (n - 1)))
    :
    ∀ q n : ℤ,
      ∃ f : ((I'.secondFiltration n).step q : C) ⟶
        ((J'.secondFiltration (n - 1)).step (q - 1) : C),
        f ≫ ((J'.secondFiltration (n - 1)).step (q - 1)).arrow =
          ((I'.secondFiltration n).step q).arrow ≫ H.hom n (n - 1) := by
  classical
  intro q n
  let Q := (J'.secondFiltration (n - 1)).step (q - 1)
  have hQ : Q.Factors (((I'.secondFiltration n).step q).arrow ≫ H.hom n (n - 1)) := by
    dsimp [HomologicalComplex₂.secondFiltration]
    apply HomologicalComplex₂.factors_finset_sup (Finset.Icc q n)
      (fun i ↦ I'.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n) _ Q
    intro i hi
    have hqi : q ≤ i := (Finset.mem_Icc.mp hi).1
    have hsum : (n - i) + i = n := by omega
    rw [I'.ιTotalOrZero_eq _ (n - i) i n hsum]
    rw [hcomp (n - i) i n hsum]
    apply Subobject.factors_add
    · apply Subobject.factors_of_factors_right (s1 (n - i) i)
      apply HomologicalComplex₂.secondFiltration_inclusion_factors J'
      · exact hJ
      · omega
      · omega
    · apply HomologicalComplex₂.factors_zsmul
      apply Subobject.factors_of_factors_right (s2 (n - i) i)
      apply HomologicalComplex₂.secondFiltration_inclusion_factors J'
      · exact hJ
      · omega
      · omega
  exact ⟨Q.factorThru _ hQ, Subobject.factorThru_arrow _ _ _⟩

end CategoryTheory
