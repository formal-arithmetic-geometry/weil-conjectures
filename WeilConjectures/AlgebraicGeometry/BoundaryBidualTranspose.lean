/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-! # Bidual transpose identities for an exceptional pairing

Source: Weil blueprint, cor-weil-boundary-duality-discharge, second proof paragraph
(blueprint: lem-weil-boundary-bidual-transpose).

The internal Hom and the canonical bidual arrow are the published closed-category
constructions. Mathlib curries a left tensor factor; the displayed braidings convert
this to the node's convention of currying the right tensor factor. The comparison
is defined only on the chosen full subcategory, with ambient tensor targets.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uT vT uZ vZ

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace CategoryTheory.BoundaryBidualTranspose

variable {T : Type uT} [Category.{vT} T] [MonoidalCategory T]
  [SymmetricCategory T] [MonoidalClosed T]
  {Z : Type uZ} [Category.{vZ} Z] [MonoidalCategory Z]
  [SymmetricCategory Z] [MonoidalClosed Z]
  (ωT : T) (ωZ : Z) (s G : T ⥤ Z) (h : G.obj ωT ≅ ωZ)
  (ST : ObjectProperty T)
  (hDT : ∀ K : T, ST K → ST ((ihom K).obj ωT))
  (q : ∀ (M N : T), ST M → ST N → (s.obj M ⊗ G.obj N ⟶ G.obj (M ⊗ N)))

/-- The specified pairing r_K, with right evaluation written as symmetry then
Mathlib evaluation. Source: cor-weil-boundary-duality-discharge, second proof paragraph
(blueprint: lem-weil-boundary-bidual-transpose). -/
def exceptionalPairing (K : T) (hK : ST K) :
    G.obj ((ihom K).obj ωT) ⊗ s.obj K ⟶ ωZ :=
  (β_ (G.obj ((ihom K).obj ωT)) (s.obj K)).hom ≫
    q K ((ihom K).obj ωT) hK (hDT K hK) ≫
    G.map ((β_ K ((ihom K).obj ωT)).hom ≫
      (β_ ((ihom K).obj ωT) K).hom ≫ (ihom.ev K).app ωT) ≫ h.hom

/-- The specified alpha_K is the right-factor transpose of r_K.
Source: cor-weil-boundary-duality-discharge, second proof paragraph
(blueprint: lem-weil-boundary-bidual-transpose). -/
def alpha (K : T) (hK : ST K) :
    G.obj ((ihom K).obj ωT) ⟶ (ihom (s.obj K)).obj ωZ :=
  curry ((β_ (s.obj K) (G.obj ((ihom K).obj ωT))).hom ≫
    exceptionalPairing ωT ωZ s G h ST hDT q K hK)

/-- The specified c_L is G(delta_L) followed by alpha at D_T L.
Source: cor-weil-boundary-duality-discharge, second proof paragraph
(blueprint: lem-weil-boundary-bidual-transpose). -/
def bidualComposite (L : T) (hL : ST L) :
    G.obj L ⟶ (ihom (s.obj ((ihom L).obj ωT))).obj ωZ :=
  G.map (toIhomIhom ωT L) ≫ alpha ωT ωZ s G h ST hDT q
    ((ihom L).obj ωT) (hDT L hL)

/-- The specified b_L, the exceptional comparison followed by mapped right evaluation.
Source: cor-weil-boundary-duality-discharge, second proof paragraph
(blueprint: lem-weil-boundary-bidual-transpose). -/
def boundaryPairing (L : T) (hL : ST L) :
    s.obj ((ihom L).obj ωT) ⊗ G.obj L ⟶ ωZ :=
  q ((ihom L).obj ωT) L (hDT L hL) hL ≫
    G.map ((β_ ((ihom L).obj ωT) L).hom ≫ (ihom.ev L).app ωT) ≫ h.hom

/-- The specified beta_L is the right-factor transpose of b_L.
Source: cor-weil-boundary-duality-discharge, second proof paragraph
(blueprint: lem-weil-boundary-bidual-transpose). -/
def beta (L : T) (hL : ST L) :
    s.obj ((ihom L).obj ωT) ⟶ (ihom (G.obj L)).obj ωZ :=
  curry ((β_ (G.obj L) (s.obj ((ihom L).obj ωT))).hom ≫
    boundaryPairing ωT ωZ s G h ST hDT q L hL)

/-- The two specified bidual transpose identities, their conditional invertibility,
and the equivalent inverse form of the second identity.
Source: cor-weil-boundary-duality-discharge, second proof paragraph
(blueprint: lem-weil-boundary-bidual-transpose).

Proof plan (the node's eight steps):
1. The tensor-Hom adjunction uncarries a into evaluation after a tensor identity;
   its inverse is injective (def-sfb-monoidal-category supplies the tensor conventions).
2. Naturality in the internal-Hom variable gives evaluation naturality for Df.
   The defining transpose of delta gives its evaluation equation.
3. Uncurry delta_P followed by D(c_L), use these two equations and symmetry
   naturality, and apply opposite_currying. The two symmetries cancel, leaving b_L.
   Injectivity identifies this with beta_L.
4. If the three listed factors are isomorphisms, functoriality makes c_L an
   isomorphism; contravariant functoriality and step 3 make beta_L an isomorphism.
5. Fullness and dual stability allow naturality of q at delta_K in its first
   argument, even though the tensor target need not lie in ST.
6. Uncurry s(delta_K) followed by beta at D_T K. Step 5 and the defining
   evaluation equation of delta_K reduce it to q followed by G of signed evaluation.
7. Uncurry delta_sK followed by D(alpha_K). Evaluation naturality, symmetry
   naturality and the transpose defining alpha_K give exactly the same map.
   Injectivity proves the second identity.
8. If alpha_K is invertible, D(alpha_K) is invertible. Postcompose with its
   inverse for the final form; conversely postcompose with D(alpha_K) and cancel.
-/
theorem bidual_transpose
    (SZ : ObjectProperty Z) [ST.IsClosedUnderIsomorphisms]
    [SZ.IsClosedUnderIsomorphisms]
    (hDZ : ∀ X : Z, SZ X → SZ ((ihom X).obj ωZ))
    (hs : ∀ K : T, ST K → SZ (s.obj K))
    (hG : ∀ K : T, ST K → SZ (G.obj K))
    (q_natural : ∀ (M M' N N' : T) (hM : ST M) (hM' : ST M')
      (hN : ST N) (hN' : ST N') (f : M ⟶ M') (g : N ⟶ N'),
      (s.map f ⊗ₘ G.map g) ≫ q M' N' hM' hN' =
        q M N hM hN ≫ G.map (f ⊗ₘ g))
    (opposite_currying : ∀ (L : T) (hL : ST L),
      (bidualComposite ωT ωZ s G h ST hDT q L hL ⊗ₘ
          𝟙 (s.obj ((ihom L).obj ωT))) ≫
        (β_ ((ihom (s.obj ((ihom L).obj ωT))).obj ωZ)
          (s.obj ((ihom L).obj ωT))).hom ≫
        (ihom.ev (s.obj ((ihom L).obj ωT))).app ωZ =
      (β_ (G.obj L) (s.obj ((ihom L).obj ωT))).hom ≫
        boundaryPairing ωT ωZ s G h ST hDT q L hL) :
    (∀ (L : T) (hL : ST L),
      beta ωT ωZ s G h ST hDT q L hL =
        toIhomIhom ωZ (s.obj ((ihom L).obj ωT)) ≫
          (internalHom.flip.obj ωZ).map
            (bidualComposite ωT ωZ s G h ST hDT q L hL).op) ∧
    (∀ (K : T) (hK : ST K),
      s.map (toIhomIhom ωT K) ≫
          beta ωT ωZ s G h ST hDT q ((ihom K).obj ωT) (hDT K hK) =
        toIhomIhom ωZ (s.obj K) ≫
          (internalHom.flip.obj ωZ).map (alpha ωT ωZ s G h ST hDT q K hK).op) ∧
    (∀ (L : T) (hL : ST L),
      IsIso (alpha ωT ωZ s G h ST hDT q ((ihom L).obj ωT) (hDT L hL)) →
      IsIso (toIhomIhom ωT L) →
      IsIso (toIhomIhom ωZ (s.obj ((ihom L).obj ωT))) →
      IsIso (bidualComposite ωT ωZ s G h ST hDT q L hL) ∧
        IsIso (beta ωT ωZ s G h ST hDT q L hL)) ∧
    (∀ (K : T) (hK : ST K) [IsIso (alpha ωT ωZ s G h ST hDT q K hK)],
      (s.map (toIhomIhom ωT K) ≫
          beta ωT ωZ s G h ST hDT q ((ihom K).obj ωT) (hDT K hK) =
        toIhomIhom ωZ (s.obj K) ≫
          (internalHom.flip.obj ωZ).map (alpha ωT ωZ s G h ST hDT q K hK).op) ↔
      s.map (toIhomIhom ωT K) ≫
          beta ωT ωZ s G h ST hDT q ((ihom K).obj ωT) (hDT K hK) ≫
          inv ((internalHom.flip.obj ωZ).map
            (alpha ωT ωZ s G h ST hDT q K hK).op) = toIhomIhom ωZ (s.obj K)) := by
  have _ := hDZ
  have _ := hs
  have _ := hG
  have first : ∀ (L : T) (hL : ST L),
      beta ωT ωZ s G h ST hDT q L hL =
        toIhomIhom ωZ (s.obj ((ihom L).obj ωT)) ≫
          (internalHom.flip.obj ωZ).map
            (bidualComposite ωT ωZ s G h ST hDT q L hL).op := by
    intro L hL
    apply uncurry_injective
    change uncurry (curry _) =
      uncurry (toIhomIhom _ _ ≫ (pre (bidualComposite ωT ωZ s G h ST hDT q L hL)).app ωZ)
    rw [uncurry_curry, uncurry_pre_app, uncurry_toIhomIhom]
    simpa only [tensorHom_id] using (opposite_currying L hL).symm
  refine ⟨first, ?_, ?_, ?_⟩
  · intro K hK
    have heval :
        (toIhomIhom ωT K ▷ (ihom K).obj ωT) ≫
          (β_ ((ihom ((ihom K).obj ωT)).obj ωT) ((ihom K).obj ωT)).hom ≫
          (ihom.ev ((ihom K).obj ωT)).app ωT = (ihom.ev K).app ωT := by
      rw [BraidedCategory.braiding_naturality_left_assoc, ← uncurry_eq,
        uncurry_toIhomIhom, SymmetricCategory.symmetry_assoc]
    have hq := q_natural K ((ihom ((ihom K).obj ωT)).obj ωT)
      ((ihom K).obj ωT) ((ihom K).obj ωT) hK (hDT _ (hDT K hK))
      (hDT K hK) (hDT K hK) (toIhomIhom ωT K) (𝟙 _)
    simp only [G.map_id, tensorHom_id] at hq
    apply uncurry_injective
    change uncurry (s.map (toIhomIhom ωT K) ≫ curry _) =
      uncurry (toIhomIhom _ _ ≫ (pre (alpha ωT ωZ s G h ST hDT q K hK)).app ωZ)
    rw [uncurry_natural_left, uncurry_curry, uncurry_pre_app, uncurry_toIhomIhom,
      BraidedCategory.braiding_naturality_left_assoc, ← uncurry_eq]
    simp only [alpha, exceptionalPairing, uncurry_curry,
      SymmetricCategory.symmetry_assoc]
    rw [BraidedCategory.braiding_naturality_right_assoc]
    unfold boundaryPairing
    rw [← Category.assoc (s.map (toIhomIhom ωT K) ▷ _) _ _, hq]
    simp only [Category.assoc]
    rw [← Category.assoc (G.map _) (G.map _) h.hom, ← G.map_comp, heval]
  · intro L hL hα hδ hδs
    have : IsIso (bidualComposite ωT ωZ s G h ST hDT q L hL) := by
      unfold bidualComposite
      infer_instance
    refine ⟨inferInstance, ?_⟩
    rw [first L hL]
    infer_instance
  · intro K hK hα
    let a := s.map (toIhomIhom ωT K) ≫
      beta ωT ωZ s G h ST hDT q ((ihom K).obj ωT) (hDT K hK)
    let b := toIhomIhom ωZ (s.obj K)
    let d := (internalHom.flip.obj ωZ).map (alpha ωT ωZ s G h ST hDT q K hK).op
    simpa only [a, b, d, Category.assoc] using (IsIso.comp_inv_eq d (f := a) (g := b)).symm

end CategoryTheory.BoundaryBidualTranspose
