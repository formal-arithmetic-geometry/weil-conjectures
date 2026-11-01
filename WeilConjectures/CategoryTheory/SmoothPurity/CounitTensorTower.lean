/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction

/-! # Tensor counit squares in an ordered tower -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory
open AlgebraicGeometry.Etale

/-- Counit squares paste along an ordered tower of adjunctions.
Source: affine-space top trace proof, ordered coordinate induction; adjunction naturality
(blueprint: lem-pur-counit-tensor-tower).

Proof: at zero both exchanges and both counits are identities. At a successor,
expand the two composite counits. Move the preceding right comparison through the
inner counit by its naturality, then apply the given one-step counit square. The
naturality of the preceding left exchange moves the resulting inner counit to the
left of that exchange. Apply the induction hypothesis and functoriality of B zero.
This is the same formal pasting calculation as the coordinate base-change tower;
it applies in particular to tensor coefficient endofunctors. -/
theorem counitTensor_tower {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {L' : ∀ d, C' (d + 1) ⥤ C' d}
    {R : ∀ d, C d ⥤ C (d + 1)} {R' : ∀ d, C' d ⥤ C' (d + 1)}
    (a : ∀ d, L d ⊣ R d) (a' : ∀ d, L' d ⊣ R' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ≅ (R' d).obj ((B d).obj K))
    (h : ∀ d K, (e d).app ((R d).obj K) ≫
      (L' d).map (r d K).hom ≫ (a' d).counit.app ((B d).obj K) =
        (B d).map ((a d).counit.app K)) (d : ℕ) (K : C 0) :
    (affineTraceExchangeTower L L' B e d).app ((affineTraceRightTower R d).obj K) ≫
      (affineTraceLeftTower L' d).map (affineTraceRightExchangeTower R R' B r d K).hom ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) =
    (B 0).map ((affineTraceAdjunctionTower a d).counit.app K) := by
  induction d with
  | zero =>
    rw [affineTraceExchangeTower_zero]
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = (B 0).map (𝟙 K)
    simp
  | succ d ih =>
    let M := (affineTraceRightTower R d).obj K
    let q := affineTraceRightExchangeTower R R' B r d K
    have hn := (a' d).counit.naturality q.hom
    simp only [Functor.comp_map, Functor.id_map] at hn
    have hi : (e d).app ((R d).obj M) ≫
        (L' d).map ((r d M).hom ≫ (R' d).map q.hom) ≫
        (a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K)) =
        (B d).map ((a d).counit.app M) ≫ q.hom := by
      rw [Functor.map_comp, Category.assoc, hn]
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ q.hom) (h d M)
    rw [affineTraceExchangeTower_succ, affineTraceAdjunctionTower_counit_succ,
      affineTraceAdjunctionTower_counit_succ]
    change (_ ≫ (affineTraceLeftTower L' d).map ((e d).app ((R d).obj M))) ≫
      (affineTraceLeftTower L' d).map
        ((L' d).map ((r d M).hom ≫ (R' d).map q.hom)) ≫
      (affineTraceLeftTower L' d).map
        ((a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K))) ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) = _
    have hi' := congrArg (fun z ↦ (affineTraceLeftTower L' d).map z) hi
    simp only [Functor.map_comp, Category.assoc] at hi'
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hi']
    have he := (affineTraceExchangeTower L L' B e d).naturality ((a d).counit.app M)
    simp only [Functor.comp_map] at he
    change _ ≫ (affineTraceExchangeTower L L' B e d).app M =
      (affineTraceExchangeTower L L' B e d).app
        ((L d).obj ((affineTraceRightTower R (d + 1)).obj K)) ≫ _ at he
    rw [← Category.assoc, ← Category.assoc, ← he]
    simp only [Category.assoc]
    rw [ih, ← Functor.map_comp]

end CategoryTheory
