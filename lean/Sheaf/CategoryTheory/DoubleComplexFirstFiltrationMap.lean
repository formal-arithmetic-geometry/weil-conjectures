/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.CategoryTheory.DoubleComplexTotal

/-! # Bicomplex maps preserve the first total filtration

Source: Stacks Project, Tag 015K
(blueprint: lem-weil-pbc-total-first-filtration-map).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

/-- A bidegree-preserving map preserves each finite image-sum filtration step.
Source: Stacks Project, Tag 015K
(blueprint: lem-weil-pbc-total-first-filtration-map).

Proof: the total map carries each diagonal inclusion to the corresponding target
inclusion composed with its bidegree component. This composite factors through
its image and then through the target finite supremum. Pull back that target
subobject along the total map. Each source image lies in the pullback, so their
finite supremum lies in it. The pullback universal property supplies the claimed
factorization. This argument needs no vanishing or injectivity hypotheses. -/
theorem firstFiltration_map
    {C : Type u} [Category.{v} C] [Abelian C]
    (K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (φ : K ⟶ L) (r n : ℤ) :
    ∃ f : ((K.firstFiltration n).step r : C) ⟶
      ((L.firstFiltration n).step r : C),
      f ≫ ((L.firstFiltration n).step r).arrow =
        ((K.firstFiltration n).step r).arrow ≫
          (total.map φ (ComplexShape.up ℤ)).f n := by
  classical
  let g := (total.map φ (ComplexShape.up ℤ)).f n
  let Q := (L.firstFiltration n).step r
  let P := (Subobject.pullback g).obj Q
  have h : (K.firstFiltration n).step r ≤ P := by
    change (Finset.Icc r n).sup _ ≤ P
    apply Finset.sup_le
    intro i hi
    let a := K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n
    have hQ : Q.Factors (a ≫ g) := by
      dsimp [a, g]
      rw [ιTotalOrZero_map]
      change Subobject.Factors ((Finset.Icc r n).sup
        (fun j ↦ imageSubobject (L.ιTotalOrZero (ComplexShape.up ℤ) j (n - j) n))) _
      apply Subobject.finset_sup_factors
      exact ⟨i, hi, imageSubobject_factors_comp_self _ _⟩
    have hP : P.Factors a := pullback_factors g Q a hQ
    exact imageSubobject_le a (P.factorThru a hP) (P.factorThru_arrow a hP)
  have hP := Subobject.factors_of_le ((K.firstFiltration n).step r).arrow h
    (Subobject.factors_self _)
  have hQ := (pullback_factors_iff g Q _).mp hP
  exact ⟨Q.factorThru _ hQ, Q.factorThru_arrow _ hQ⟩

end HomologicalComplex₂
