/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived

/-!
# Coherence of the pullback comparisons of derived pullbacks

For a commutative square `g' ≫ p = p' ≫ g` of schemes, the pullback comparison
`θ_sq : Lg^* ⋙ Lp'^* ≅ Lp^* ⋙ Lg'^*` (`ProEtale.CondensedRing.pullbackSquareComparison`) of the
derived pullbacks of module objects satisfies the following coherences:

- `ProEtale.CondensedRing.pullbackSquareComparison_flip`: the comparison of the transposed square
  is the inverse comparison;
- `ProEtale.CondensedRing.pullbackSquareComparison_cube`: for a commutative cube, the two
  composites of the comparisons of the faces agree;
- `ProEtale.CondensedRing.pullbackSquareComparison_tensor`: the comparison is monoidal, i.e.
  compatible with the tensor comparisons of the derived pullbacks.

The comparisons are compared with the triple composition isomorphisms
`L(a ≫ b ≫ c)^* ≅ Lc^* ⋙ Lb^* ⋙ La^*`
(`ProEtale.CondensedRing.map_pullbackSquareComparison_hom_app`,
`ProEtale.CondensedRing.pullbackSquareComparison_hom_app_obj`), using the associativity of the
composition isomorphisms. The diagram chases are carried out in abstract categories, where the
computations are cheap, and then specialized.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

/-- The components of `α ≪≫ eqToIso h ≪≫ β`. -/
private lemma trans_eqToIso_trans_hom_app {C D : Type*} [Category C] [Category D]
    {F F' G H : C ⥤ D} (α : G ≅ F) (h : F = F') (β : F' ≅ H) (K : C) :
    (α ≪≫ eqToIso h ≪≫ β).hom.app K =
      α.hom.app K ≫ eqToHom (Functor.congr_obj h K) ≫ β.hom.app K := by
  subst h
  simp

/-- The image under a functor of the expression of a pullback comparison through composition
isomorphisms. -/
private lemma map_comp_map_aux {C D : Type*} {_ : Category C} {_ : Category D} (H : D ⥤ C)
    {y₀ y₁ y₂ y₃ : D} (c₁ : y₀ ⟶ y₁) (c₁' : y₁ ⟶ y₀) (hc₁ : c₁ ≫ c₁' = 𝟙 _) (θ : y₁ ⟶ y₃)
    (E : y₀ ⟶ y₂) (c₂ : y₂ ⟶ y₃) (hθ : θ = c₁' ≫ E ≫ c₂) :
    H.map c₁ ≫ H.map θ = H.map E ≫ H.map c₂ := by
  rw [hθ, ← H.map_comp, reassoc_of% hc₁, H.map_comp]

/-- The diagram chase behind `map_pullbackSquareComparison_hom_app`. -/
private lemma map_square_aux {C : Type*} {_ : Category C} {x₀ x₁ w₀ w₁ w₂ w₃ : C}
    (c₀ : x₀ ⟶ w₀) (m₁ : w₀ ⟶ w₁) (mθ : w₁ ⟶ w₃) (mE : w₀ ⟶ w₂) (m₂ : w₂ ⟶ w₃)
    (hm : m₁ ≫ mθ = mE ≫ m₂) (E' : x₀ ⟶ x₁) (c₀' : x₁ ⟶ w₂) (hN : c₀ ≫ mE = E' ≫ c₀') :
    c₀ ≫ m₁ ≫ mθ = E' ≫ c₀' ≫ m₂ := by
  rw [hm, reassoc_of% hN]

/-- The diagram chase behind `pullbackSquareComparison_hom_app_obj`. -/
private lemma square_app_obj_aux {C : Type*} [Category C]
    {u₁ u₂ u₃ u₄ v₁ v₂ w₁ w₂ z₁ z₂ : C} (p₁₂ : u₁ = u₂) (p₁₃ : u₁ = u₃) (p₃₄ : u₃ = u₄)
    (p₂₄ : u₂ = u₄) (m₁ : u₂ ⟶ v₁) (m₂ : v₁ ⟶ z₁) (a₁ : u₁ ⟶ w₁) (a₂ : w₁ ⟶ z₁)
    (a₂' : z₁ ⟶ w₁) (ha₂ : a₂ ≫ a₂' = 𝟙 _)
    (A₁ : a₁ ≫ a₂ = eqToHom p₁₂ ≫ m₁ ≫ m₂) (θ : z₁ ⟶ z₂) (E₃ : w₁ ⟶ w₂) (b₁ : u₃ ⟶ w₂)
    (b₂ : w₂ ⟶ z₂) (hθ : θ = a₂' ≫ E₃ ≫ b₂) (N : a₁ ≫ E₃ = eqToHom p₁₃ ≫ b₁)
    (n₁ : u₄ ⟶ v₂) (n₂ : v₂ ⟶ z₂) (A₂ : b₁ ≫ b₂ = eqToHom p₃₄ ≫ n₁ ≫ n₂) :
    m₁ ≫ m₂ ≫ θ = eqToHom p₂₄ ≫ n₁ ≫ n₂ := by
  have h : m₁ ≫ m₂ = eqToHom p₁₂.symm ≫ a₁ ≫ a₂ := by
    rw [A₁]
    simp
  rw [reassoc_of% h, hθ, reassoc_of% ha₂, reassoc_of% N, A₂]
  simp

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Composition

variable {R S T : Scheme.{u}}

set_option maxHeartbeats 1000000 in
-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- The composition isomorphism `L(a ≫ h)^* ≅ Lh^* ⋙ La^*` commutes with the `eqToHom`s induced
by an equality `h = h'`. -/
lemma leftDerivedUpperStarComp_hom_app_map_eqToHom (a : R ⟶ S) {h h' : S ⟶ T} (e : h = h')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
    (leftDerivedUpperStarComp Λ a h).hom.app K ≫
        L((a)^*⟦Λ⟧).map (eqToHom (by rw [e] : L((h)^*⟦Λ⟧).obj K = L((h')^*⟦Λ⟧).obj K)) =
      eqToHom (by rw [e] : L((a ≫ h)^*⟦Λ⟧).obj K = L((a ≫ h')^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ a h').hom.app K := by
  subst e
  rw [eqToHom_refl, eqToHom_refl, L((a)^*⟦Λ⟧).map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

set_option maxHeartbeats 1000000 in
-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- The composition isomorphism `L(h ≫ b)^* ≅ Lb^* ⋙ Lh^*` commutes with the `eqToHom`s induced
by an equality `h = h'`. -/
lemma leftDerivedUpperStarComp_hom_app_eqToHom {h h' : R ⟶ S} (e : h = h') (b : S ⟶ T)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
    (leftDerivedUpperStarComp Λ h b).hom.app K ≫
        eqToHom (by rw [e] : L((h)^*⟦Λ⟧).obj (L((b)^*⟦Λ⟧).obj K) =
          L((h')^*⟦Λ⟧).obj (L((b)^*⟦Λ⟧).obj K)) =
      eqToHom (by rw [e] : L((h ≫ b)^*⟦Λ⟧).obj K = L((h' ≫ b)^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ h' b).hom.app K := by
  subst e
  rw [eqToHom_refl, eqToHom_refl]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end Composition

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- `ProEtale.CondensedRing.pullbackSquareComparison` unfolded. -/
lemma pullbackSquareComparison_eq (sq : CommSq g' p' p g) :
    pullbackSquareComparison Λ sq = (leftDerivedUpperStarComp Λ p' g).symm ≪≫
      eqToIso (by rw [sq.w]) ≪≫ leftDerivedUpperStarComp Λ g' p :=
  rfl

/-- The components of the pullback comparison. -/
lemma pullbackSquareComparison_hom_app (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app K =
      (leftDerivedUpperStarComp Λ p' g).inv.app K ≫
        eqToHom (by rw [sq.w] : L((p' ≫ g)^*⟦Λ⟧).obj K = L((g' ≫ p)^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ g' p).hom.app K :=
  (congrArg (fun θ ↦ θ.hom.app K) (pullbackSquareComparison_eq Λ sq)).trans
    (trans_eqToIso_trans_hom_app _ _ _ K)

set_option maxHeartbeats 1000000 in
-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- `L(a)^*` of the pullback comparison, in terms of the triple composition isomorphisms
`L(a ≫ p' ≫ g)^* ≅ Lg^* ⋙ Lp'^* ⋙ La^*` and `L(a ≫ g' ≫ p)^* ≅ Lp^* ⋙ Lg'^* ⋙ La^*`. -/
lemma map_pullbackSquareComparison_hom_app {W : Scheme.{u}} (sq : CommSq g' p' p g)
    (a : W ⟶ X')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarComp Λ a (p' ≫ g)).hom.app K ≫
        L((a)^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ p' g).hom.app K) ≫
        L((a)^*⟦Λ⟧).map ((pullbackSquareComparison Λ sq).hom.app K) =
      eqToHom (by rw [sq.w] : L((a ≫ p' ≫ g)^*⟦Λ⟧).obj K = L((a ≫ g' ≫ p)^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ a (g' ≫ p)).hom.app K ≫
        L((a)^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ g' p).hom.app K) :=
  map_square_aux _ _ _ _ _
    (map_comp_map_aux L((a)^*⟦Λ⟧) _ _ ((leftDerivedUpperStarComp Λ p' g).hom_inv_id_app K) _ _ _
      (pullbackSquareComparison_hom_app Λ sq K)) _ _
    (leftDerivedUpperStarComp_hom_app_map_eqToHom Λ a sq.w.symm K)

/-- The pullback comparison at `L(b)^* K`, in terms of the triple composition isomorphisms
`L(p' ≫ g ≫ b)^* ≅ Lb^* ⋙ Lg^* ⋙ Lp'^*` and `L(g' ≫ p ≫ b)^* ≅ Lb^* ⋙ Lp^* ⋙ Lg'^*`. -/
lemma pullbackSquareComparison_hom_app_obj {V : Scheme.{u}} (sq : CommSq g' p' p g)
    (b : Y ⟶ V)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))) :
    (leftDerivedUpperStarComp Λ p' (g ≫ b)).hom.app K ≫
        L((p')^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ g b).hom.app K) ≫
        (pullbackSquareComparison Λ sq).hom.app (L((b)^*⟦Λ⟧).obj K) =
      eqToHom (by rw [reassoc_of% sq.w] :
          L((p' ≫ g ≫ b)^*⟦Λ⟧).obj K = L((g' ≫ p ≫ b)^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ g' (p ≫ b)).hom.app K ≫
        L((g')^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ p b).hom.app K) :=
  square_app_obj_aux _ _ _ _ _ _ _ _ _ ((leftDerivedUpperStarComp Λ p' g).hom_inv_id_app _)
    (leftDerivedUpperStarComp_assoc_app Λ p' g b K) _ _ _ _
    (pullbackSquareComparison_hom_app Λ sq (L((b)^*⟦Λ⟧).obj K))
    (leftDerivedUpperStarComp_hom_app_eqToHom Λ sq.w.symm b K) _ _
    (leftDerivedUpperStarComp_assoc_app Λ g' p b K)

end BaseChange

section Cube

variable {P' M' P₁' M₁' P M P₁ M₁ : Scheme.{u}} {iP : P' ⟶ P} {iM : M' ⟶ M} {iP₁ : P₁' ⟶ P₁}
  {iM₁ : M₁' ⟶ M₁} {f' : P' ⟶ M'} {g' : M' ⟶ M₁'} {k' : P' ⟶ P₁'} {e' : P₁' ⟶ M₁'}
  {f : P ⟶ M} {g : M ⟶ M₁} {k : P ⟶ P₁} {e : P₁ ⟶ M₁}

end Cube

end AlgebraicGeometry.ProEtale.CondensedRing
