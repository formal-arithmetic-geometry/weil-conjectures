/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing

/-! # Coherence of native condensed derived pullback comparisons

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, paragraphs 2–3
(blueprint: lem-fix-condensed-pullback-coherence).

The native compositor, its associativity and unit laws, and its tensor and coefficient-unit
compatibilities already exist upstream. This module proves the remaining explicit square
unit and pasting equations, using those same native comparisons on the unbounded categories.
The upstream square comparison has the reverse orientation from the square in the node;
its inverse is the comparison in that orientation, by `pullbackSquareComparison_flip`.

Expand a square as inverse compositor, equality transport and compositor. The compositor's
coefficient-unit equation proves the square's coefficient-unit equation. Its two unit laws
prove the identity-square equation. For horizontal pasting, precompose with the lower boundary
compositor, use associativity, then `map_pullbackSquareComparison_hom_app` and
`pullbackSquareComparison_hom_app_obj`, and cancel the interior compositors. Vertical pasting
is horizontal pasting for the transposed squares, inverted using the flip equation.

The public imports also supply the other clauses of the node: compositor associativity and
unit laws, tensor and coefficient-unit compatibility, the normalized conjugate direct-image
compositor, and square tensor and cube coherence. These native results make the longer
section-action and resolution-transport proof route unnecessary here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem paste_horizontal_aux {C : Type*} [Category C]
    {d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ : C}
    (c₀ : d₀ ≅ d₁) (c₁ : d₂ ≅ d₃) (θ : d₁ ⟶ d₃)
    (c₂ : d₁ ⟶ d₄) (mθ : d₄ ⟶ d₅) (θ' : d₅ ⟶ d₆)
    (m : d₃ ⟶ d₆) (mi : d₆ ⟶ d₃)
    (a₀ : d₇ ⟶ d₈) (a₁ : d₈ ⟶ d₄) (b₀ : d₉ ⟶ d₁₀) (b₁ : d₁₀ ⟶ d₅)
    (e₀ : d₀ = d₂) (e₁ : d₀ = d₇) (e₂ : d₇ = d₉) (e₃ : d₉ = d₂)
    (hθ : θ = c₀.inv ≫ eqToHom e₀ ≫ c₁.hom)
    (ha : c₀.hom ≫ c₂ = eqToHom e₁ ≫ a₀ ≫ a₁)
    (hb : a₀ ≫ a₁ ≫ mθ = eqToHom e₂ ≫ b₀ ≫ b₁)
    (hc : b₀ ≫ b₁ ≫ θ' = eqToHom e₃ ≫ c₁.hom ≫ m)
    (hm : m ≫ mi = 𝟙 _) :
    θ = c₂ ≫ mθ ≫ θ' ≫ mi := by
  rw [← cancel_epi c₀.hom, hθ]
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, hm]
  simp

private theorem inverse_paste_aux {C : Type*} [Category C] {x y a b c : C}
    (θ : x ≅ y) (α : x ≅ a) (β : a ≅ b) (γ : b ≅ c) (δ : y ≅ c)
    (h : θ.inv = δ.hom ≫ γ.inv ≫ β.inv ≫ α.inv) :
    θ.hom = α.hom ≫ β.hom ≫ γ.hom ≫ δ.inv := by
  apply (Iso.inv_eq_inv θ (α ≪≫ β ≪≫ γ ≪≫ δ.symm)).mp
  simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc] using h

/-- The commuting-square comparison preserves the coefficient unit.

Source: the cited blueprint proof, paragraphs 2–3
(blueprint: lem-fix-condensed-pullback-coherence).
Proof: use `pullbackSquareComparison_eq` to expand the comparison as the inverse native
compositor, the equality transport, and the native compositor. Apply
`leftDerivedUpperStarComp_hom_app_unit` to each compositor. Transport along the square's
commutativity identifies their coefficient maps; the middle compositor and its inverse
cancel. This is valid for every commutative condensed ring and every scheme square. -/
theorem pullbackSquareComparison_unit {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) :
    (pullbackSquareComparison Λ sq).hom.app (𝟙_ _) ≫
        L((g')^*⟦Λ⟧).map (leftDerivedUpperStarUnitIso Λ p).hom ≫
        (leftDerivedUpperStarUnitIso Λ g').hom =
      L((p')^*⟦Λ⟧).map (leftDerivedUpperStarUnitIso Λ g).hom ≫
        (leftDerivedUpperStarUnitIso Λ p').hom := by
  have transport {f₁ f₂ : X' ⟶ Y} (e : f₁ = f₂) :
      eqToHom (by rw [e] : L((f₁)^*⟦Λ⟧).obj (𝟙_ _) =
        L((f₂)^*⟦Λ⟧).obj (𝟙_ _)) ≫ (leftDerivedUpperStarUnitIso Λ f₂).hom =
      (leftDerivedUpperStarUnitIso Λ f₁).hom := by
    subst e
    simp
  rw [pullbackSquareComparison_hom_app, Category.assoc, Category.assoc,
    leftDerivedUpperStarComp_hom_app_unit, transport sq.w.symm]
  rw [← leftDerivedUpperStarComp_hom_app_unit Λ p' g]
  simp

/-- Identity vertical arrows give the identity pullback comparison after the canonical
identity-functor comparisons.

Source: the cited blueprint proof, paragraphs 2–3
(blueprint: lem-fix-condensed-pullback-coherence).
Proof: expand `pullbackSquareComparison` into the two native compositors and transport.
The left and right unit laws `leftDerivedUpperStarComp_id_left_app` and
`leftDerivedUpperStarComp_id_right_app` identify the two boundary expansions with the
canonical identity comparison. Cancel the inverse compositor. -/
theorem pullbackSquareComparison_identity {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ
      (CommSq.mk ((Category.id_comp f).trans (Category.comp_id f).symm))).hom.app K ≫
        (leftDerivedUpperStarId Λ X).hom.app (L((f)^*⟦Λ⟧).obj K) =
      L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app K) := by
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ f (𝟙 Y)).hom.app K)]
  rw [pullbackSquareComparison_hom_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [leftDerivedUpperStarComp_id_left_app, leftDerivedUpperStarComp_id_right_app]
  simp

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

set_option maxHeartbeats 20000000 in
-- Instantiating the native coherence equations unifies large derived pullback objects.
/-- Horizontal pasting of scheme squares gives the pasted native pullback comparison.

Source: the cited blueprint proof, paragraphs 2–3
(blueprint: lem-fix-condensed-pullback-coherence).
Proof: expand all three square comparisons as inverse compositor, equality transport,
and compositor. The associativity equation `leftDerivedUpperStarComp_assoc_app` identifies
the two three-edge expansions. Naturality moves equality transport past a compositor.
The two expansions through the common middle vertical edge cancel. The remaining two
boundary compositors are exactly the comparison of the outer square. No square is required
to be Cartesian, and no edge is required to be invertible. -/
theorem pullbackSquareComparison_paste_horizontal
    {A B C A' B' C' : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ C}
    {a' : A' ⟶ B'} {b' : B' ⟶ C'} {u₀ : A' ⟶ A} {v₀ : B' ⟶ B} {w₀ : C' ⟶ C}
    (sqa : CommSq u₀ a' a v₀) (sqb : CommSq v₀ b' b w₀)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C))) :
    (pullbackSquareComparison Λ (sqa.vert_comp sqb)).hom.app K =
      (leftDerivedUpperStarComp Λ a' b').hom.app (L((w₀)^*⟦Λ⟧).obj K) ≫
        L((a')^*⟦Λ⟧).map ((pullbackSquareComparison Λ sqb).hom.app K) ≫
        (pullbackSquareComparison Λ sqa).hom.app (L((b)^*⟦Λ⟧).obj K) ≫
        L((u₀)^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ a b).inv.app K) := by
  refine paste_horizontal_aux
    (c₀ := (leftDerivedUpperStarComp Λ (a' ≫ b') w₀).app K)
    (c₁ := (leftDerivedUpperStarComp Λ u₀ (a ≫ b)).app K)
    (hθ := pullbackSquareComparison_hom_app Λ (sqa.vert_comp sqb) K)
    (ha := leftDerivedUpperStarComp_assoc_app Λ a' b' w₀ K)
    (hb := map_pullbackSquareComparison_hom_app Λ sqb a' K)
    (hc := pullbackSquareComparison_hom_app_obj Λ sqa b K) (hm := ?_)
  rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rfl

/-- Vertical pasting of scheme squares gives the pasted native pullback comparison.

Source: the cited blueprint proof, paragraphs 2–3
(blueprint: lem-fix-condensed-pullback-coherence).
Proof: apply horizontal pasting to the two transposed squares. The flip equation identifies
all three transposed comparisons with the inverses of the original comparisons. Take the
inverse of this equality of isomorphisms; inverses reverse composition and commute with
functorial mapping, giving the displayed vertical-pasting formula. Together with
associativity and the identity equation this gives arbitrary finite pasting. -/
theorem pullbackSquareComparison_paste_vertical
    {X Y X' Y' X'' Y'' : Scheme.{u}}
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {p'' : X'' ⟶ Y''}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} {h' : X'' ⟶ X'} {h : Y'' ⟶ Y'}
    (sq : CommSq g' p' p g) (sq' : CommSq h' p'' p' h)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ (sq'.horiz_comp sq)).hom.app K =
      L((p'')^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ h g).hom.app K) ≫
        (pullbackSquareComparison Λ sq').hom.app (L((g)^*⟦Λ⟧).obj K) ≫
        L((h')^*⟦Λ⟧).map ((pullbackSquareComparison Λ sq).hom.app K) ≫
        (leftDerivedUpperStarComp Λ h' g').inv.app (L((p)^*⟦Λ⟧).obj K) := by
  have hpaste := pullbackSquareComparison_paste_horizontal Λ sq'.flip sq.flip K
  have hsquare : sq'.flip.vert_comp sq.flip = (sq'.horiz_comp sq).flip :=
    Subsingleton.elim _ _
  rw [hsquare] at hpaste
  rw [pullbackSquareComparison_flip Λ (sq'.horiz_comp sq),
    pullbackSquareComparison_flip Λ sq', pullbackSquareComparison_flip Λ sq] at hpaste
  exact inverse_paste_aux
    ((pullbackSquareComparison Λ (sq'.horiz_comp sq)).app K)
    (L((p'')^*⟦Λ⟧).mapIso ((leftDerivedUpperStarComp Λ h g).app K))
    ((pullbackSquareComparison Λ sq').app (L((g)^*⟦Λ⟧).obj K))
    (L((h')^*⟦Λ⟧).mapIso ((pullbackSquareComparison Λ sq).app K))
    ((leftDerivedUpperStarComp Λ h' g').app (L((p)^*⟦Λ⟧).obj K)) hpaste

set_option maxHeartbeats 20000000 in
-- Instantiating the inverse calculation unifies large derived pullback objects.
end AlgebraicGeometry.ProEtale.CondensedRing
