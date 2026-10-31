/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceThomMap

/-! # Support interchange for two leading coordinate factors

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product and even shifts
(blueprint: lem-pur-coordinate-product-head-support-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity AffineLinePurity

/-- Exchange the two outer factors of a nested pullback over a common base. -/
private def nestedSwap {T X A C : Scheme.{u}} (s : T ⟶ X) (a : A ⟶ X) (b : C ⟶ X) :
    pullback (pullback.fst s b ≫ s) a ⟶ pullback (pullback.fst s a ≫ s) b :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by simpa only [Category.assoc] using pullback.condition))
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (by
      rw [← Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc,
        pullback.condition])

private theorem nestedSwap_comp {T X A C : Scheme.{u}} (s : T ⟶ X) (a : A ⟶ X)
    (b : C ⟶ X) :
    nestedSwap s a b ≫ (pullback.fst (pullback.fst s a ≫ s) b ≫ pullback.fst s a ≫ s) =
      pullback.fst (pullback.fst s b ≫ s) a ≫ pullback.fst s b ≫ s := by
  simp only [nestedSwap, ← Category.assoc, pullback.lift_fst]

private theorem nestedSwap_swap {T X A C : Scheme.{u}} (s : T ⟶ X) (a : A ⟶ X)
    (b : C ⟶ X) : nestedSwap s a b ≫ nestedSwap s b a = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [nestedSwap]
  · simp [nestedSwap]

/-- The nested pullback supports for two leading coordinates are canonically isomorphic.
Source: the support interchange step in the ordered coordinate product proof.
(blueprint: lem-pur-coordinate-product-head-support-iso).

Proof: construct the map by the universal property of the two nested pullbacks, swapping
its two divisor projections. Construct the inverse by the same recipe in the opposite
order. The pullback projection equations prove both composites are identities, and the
composite with the ambient immersion is the original support immersion by associativity
and the pullback equations. -/
theorem coordinate_product_head_support_iso (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (c : ℕ) (i j : Fin c) (is : List (Fin c)) :
    ∃ (e : support B c (i :: j :: is) ≅ support B c (j :: i :: is)),
      e.hom ≫ supportMap B c (j :: i :: is) = supportMap B c (i :: j :: is) := by
  refine ⟨⟨nestedSwap (supportMap B c is) (inclusion B c i) (inclusion B c j),
    nestedSwap (supportMap B c is) (inclusion B c j) (inclusion B c i),
    nestedSwap_swap _ _ _, nestedSwap_swap _ _ _⟩, ?_⟩
  exact nestedSwap_comp _ _ _

end AlgebraicGeometry.ProEtale.AffineZeroPurity
