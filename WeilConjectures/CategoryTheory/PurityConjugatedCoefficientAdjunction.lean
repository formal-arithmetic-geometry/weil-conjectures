/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Purity conjugation of coefficient adjunctions

Source: Weil conjectures blueprint, `sec-smooth-purity`, `sk-lem-sp-field-extension`,
sole proof paragraph (compatibility with units, counits, purity and composition);
Stacks Project, Categories, Tag 0037 (adjunctions).
(blueprint: lem-pur-purity-conjugated-coefficient-adjunction)
-/

@[expose] public section

universe w vX vY uX uY

namespace CategoryTheory

set_option autoImplicit false

/-- Conjugating the right-adjoint coefficient comparisons by the specified purity
isomorphisms transports the adjunction, both comparison squares, the associator
cocycle and the identity normalization. The left-adjoint comparisons `b` are the
same throughout, so their cocycles and normalization are unchanged.

Source: Weil conjectures blueprint, `sk-lem-sp-field-extension`, sole proof paragraph;
Stacks Project, Categories, Tag 0037.
(blueprint: lem-pur-purity-conjugated-coefficient-adjunction)

Proof plan:
1. Compose the Hom bijection of `adjJ i` with postcomposition by `(γ i).inv`.
   Its inverse postcomposes by `(γ i).hom` before applying the original inverse.
   Naturality follows from the two original naturality laws. Apply
   `lem-weil-pbc-adjunction-of-natural-bijection` (`Adjunction.mkOfHomEquiv`).
   Evaluating at identities gives the displayed unit and counit formulas.
2. Form `a` by whiskering `γ i`, then `c`, then `(γ j).symm`. Its inverse uses
   the inverse factors in reverse order. Naturality follows from the naturality
   of these three factors, and the two inverse composites cancel.
3. Substitute into the unit square, cancel the adjacent images of `γ i` and its
   inverse, use naturality of `(γ j).inv` at `b`, then apply `hunit`.
4. Substitute into the counit square, cancel the images of `γ j` and its inverse,
   use naturality of `b` at `(γ i).hom`, then apply `hcounit`.
5. In the triple composite cancel the middle images of `γ j` and its inverse.
   Naturality of `(γ k).inv` at `αY`, the assumed `c` cocycle, and naturality of
   `αX` at `(γ i).hom` give exactly the asserted `a` cocycle.
6. For identity extensions, use the formula for `c` under `uX` and `uY`.
   Naturality of `γ i` at `uY` and of `uX` at `(γ i).hom` gives the formula for
   `a` under the same unitors. No faithfulness, conservativity, or compatibility
   between different `γ i` is used. -/
theorem purity_conjugated_coefficient_adjunction
    {I : Type w} [Preorder I]
    (X : I → Type uX) (Y : I → Type uY)
    [∀ i : I, Category.{vX} (X i)] [∀ i : I, Category.{vY} (Y i)]
    (P : ∀ i : I, X i ⥤ Y i) (J H : ∀ i : I, Y i ⥤ X i)
    (adjJ : ∀ i : I, P i ⊣ J i) (γ : ∀ i : I, H i ≅ J i)
    (CX : ∀ (i j : I), i ≤ j → (X i ⥤ X j))
    (CY : ∀ (i j : I), i ≤ j → (Y i ⥤ Y j))
    (b : ∀ (i j : I) (hij : i ≤ j), P i ⋙ CY i j hij ≅ CX i j hij ⋙ P j)
    (c : ∀ (i j : I) (hij : i ≤ j), J i ⋙ CX i j hij ≅ CY i j hij ⋙ J j)
    (hunit : ∀ (i j : I) (hij : i ≤ j) (M : X i),
      (CX i j hij).map ((adjJ i).unit.app M) ≫
        (c i j hij).hom.app ((P i).obj M) ≫ (J j).map ((b i j hij).hom.app M) =
          (adjJ j).unit.app ((CX i j hij).obj M))
    (hcounit : ∀ (i j : I) (hij : i ≤ j) (K : Y i),
      (b i j hij).hom.app ((J i).obj K) ≫ (P j).map ((c i j hij).hom.app K) ≫
        (adjJ j).counit.app ((CY i j hij).obj K) =
          (CY i j hij).map ((adjJ i).counit.app K)) :
    ∃ (adjH : ∀ i : I, P i ⊣ H i)
      (a : ∀ (i j : I) (hij : i ≤ j), H i ⋙ CX i j hij ≅ CY i j hij ⋙ H j),
      (∀ (i : I) (M : X i),
        (adjH i).unit.app M = (adjJ i).unit.app M ≫ (γ i).inv.app ((P i).obj M)) ∧
      (∀ (i : I) (K : Y i),
        (adjH i).counit.app K = (P i).map ((γ i).hom.app K) ≫
          (adjJ i).counit.app K) ∧
      (∀ (i j : I) (hij : i ≤ j) (K : Y i),
        (a i j hij).hom.app K = (CX i j hij).map ((γ i).hom.app K) ≫
          (c i j hij).hom.app K ≫ (γ j).inv.app ((CY i j hij).obj K)) ∧
      (∀ (i j : I) (hij : i ≤ j) (M : X i),
        (CX i j hij).map ((adjH i).unit.app M) ≫
          (a i j hij).hom.app ((P i).obj M) ≫ (H j).map ((b i j hij).hom.app M) =
            (adjH j).unit.app ((CX i j hij).obj M)) ∧
      (∀ (i j : I) (hij : i ≤ j) (K : Y i),
        (b i j hij).hom.app ((H i).obj K) ≫ (P j).map ((a i j hij).hom.app K) ≫
          (adjH j).counit.app ((CY i j hij).obj K) =
            (CY i j hij).map ((adjH i).counit.app K)) ∧
      (∀
        (αX : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
          CX i j hij ⋙ CX j k hjk ≅ CX i k (le_trans hij hjk))
        (αY : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
          CY i j hij ⋙ CY j k hjk ≅ CY i k (le_trans hij hjk)),
        (∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (K : Y i),
          (CX j k hjk).map ((c i j hij).hom.app K) ≫
            (c j k hjk).hom.app ((CY i j hij).obj K) ≫
            (J k).map ((αY i j k hij hjk).hom.app K) =
              (αX i j k hij hjk).hom.app ((J i).obj K) ≫
                (c i k (le_trans hij hjk)).hom.app K) →
        ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (K : Y i),
          (CX j k hjk).map ((a i j hij).hom.app K) ≫
            (a j k hjk).hom.app ((CY i j hij).obj K) ≫
            (H k).map ((αY i j k hij hjk).hom.app K) =
              (αX i j k hij hjk).hom.app ((H i).obj K) ≫
                (a i k (le_trans hij hjk)).hom.app K) ∧
      (∀ (i : I) (uX : CX i i (le_refl i) ≅ 𝟭 (X i))
        (uY : CY i i (le_refl i) ≅ 𝟭 (Y i)),
        (∀ M : X i, (b i i (le_refl i)).hom.app M =
          uY.hom.app ((P i).obj M) ≫ (P i).map (uX.inv.app M)) →
        (∀ K : Y i, (c i i (le_refl i)).hom.app K =
          uX.hom.app ((J i).obj K) ≫ (J i).map (uY.inv.app K)) →
        ∀ K : Y i, (a i i (le_refl i)).hom.app K =
          uX.hom.app ((H i).obj K) ≫ (H i).map (uY.inv.app K)) := by
  let adjH : ∀ i : I, P i ⊣ H i := fun i ↦ (adjJ i).ofNatIsoRight (γ i).symm
  let a : ∀ (i j : I) (hij : i ≤ j), H i ⋙ CX i j hij ≅ CY i j hij ⋙ H j :=
    fun i j hij ↦ Functor.isoWhiskerRight (γ i) (CX i j hij) ≪≫ c i j hij ≪≫
      Functor.isoWhiskerLeft (CY i j hij) (γ j).symm
  have hu (i : I) (M : X i) :
      (adjH i).unit.app M = (adjJ i).unit.app M ≫ (γ i).inv.app ((P i).obj M) := by
    simp [adjH]
  have he (i : I) (K : Y i) :
      (adjH i).counit.app K =
        (P i).map ((γ i).hom.app K) ≫ (adjJ i).counit.app K := by
    simp [adjH]
  have ha (i j : I) (hij : i ≤ j) (K : Y i) :
      (a i j hij).hom.app K = (CX i j hij).map ((γ i).hom.app K) ≫
        (c i j hij).hom.app K ≫ (γ j).inv.app ((CY i j hij).obj K) := by
    simp [a]
  refine ⟨adjH, a, hu, he, ha, ?_, ?_, ?_, ?_⟩
  · intro i j hij M
    simp only [hu, ha, Functor.map_comp, Category.assoc]
    erw [((γ i).app ((P i).obj M)).map_inv_hom_id_assoc (CX i j hij)]
    rw [← (γ j).inv.naturality]
    simpa only [Category.assoc, Functor.comp_obj, Functor.id_obj] using congrArg
      (fun f ↦ f ≫ (γ j).inv.app ((P j).obj ((CX i j hij).obj M))) (hunit i j hij M)
  · intro i j hij K
    simp only [he, ha, Functor.map_comp, Category.assoc]
    erw [((γ j).app ((CY i j hij).obj K)).map_inv_hom_id_assoc (P j)]
    have hb := (b i j hij).hom.naturality ((γ i).hom.app K)
    simp only [Functor.comp_map] at hb
    simp only [← Category.assoc]
    rw [← hb]
    simp only [Category.assoc]
    rw [hcounit]
  · intro αX αY hc i j k hij hjk K
    simp only [ha, Functor.map_comp, Category.assoc]
    erw [((γ j).app ((CY i j hij).obj K)).map_inv_hom_id_assoc (CX j k hjk)]
    rw [← (γ k).inv.naturality]
    have hh := congrArg
      (fun f ↦ (CX j k hjk).map ((CX i j hij).map ((γ i).hom.app K)) ≫
        f ≫ (γ k).inv.app ((CY i k (le_trans hij hjk)).obj K))
      (hc i j k hij hjk K)
    simp only [Category.assoc] at hh
    rw [hh]
    have hn := (αX i j k hij hjk).hom.naturality ((γ i).hom.app K)
    simp only [Functor.comp_map] at hn
    simp only [← Category.assoc]
    rw [hn]
  · intro i uX uY _ hb K
    simp only [ha, hb, Category.assoc]
    simp

end CategoryTheory
