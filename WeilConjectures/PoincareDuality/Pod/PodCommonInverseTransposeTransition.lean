/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.PodPartialHomNaturality
public import WeilConjectures.CategoryTheory.StageSystem.Basic

/-! # Stage transitions of conjugated rational inverse transposition

The stage transitions of the algebraically closed coefficient system carry the rational
inverse transposition at a finite stage, conjugated by the common-stage tensor and Hom
comparisons, to the conjugated rational inverse transposition at a larger stage.

## Main statements

* `inverseTranspose_transition_of_scalar`: the formal statement for a transition functor
  isomorphic to a scalar extension along which inverse transposition is compatible.
* `stageComparison_endpoint_tower`, `stageComparison_scalar_tower`: the tower equation of
  stage comparisons followed by input associators.

## Implementation details

The transition is replaced by the scalar extension, the conjugating comparisons are moved
across it by their tower equations, and the remaining input associators are absorbed by
naturality of inverse transposition in the parameter and in the permitted Hom pair.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe a b c d
open CategoryTheory Opposite
namespace WeilConjectures

section Abstract
variable {C : Type a} {D : Type c}
  [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
  {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
  {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}

/-- Let `T` be a functor isomorphic to `G`, along which inverse transposition is compatible,
conjugated by a tensor comparison `τ` and a Hom comparison `η`. Then `T`, conjugated by
input associators, carries inverse transposition conjugated by the comparisons `cT`, `cH` to
inverse transposition conjugated by `cT'`, `cH'`, provided these comparisons satisfy the
displayed tower equations and inverse transposition at the target is natural in the pair. -/
theorem inverseTranspose_transition_of_scalar
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (hSD : ∀ (X : D) (P Q : K.FullSubcategory) (f : P ⟶ Q) (φ : X ⟶ HD.obj P),
      (SD.transpose X Q).symm (φ ≫ HD.map f) =
        TD.map (Prod.mkHom (𝟙 X) f.hom.1.unop) ≫ (SD.transpose X P).symm φ ≫ f.hom.2)
    (T G : C ⥤ D) (e : T ≅ G)
    (L : C) (P : J.FullSubcategory) (X H : C) (L' : D) (P' : K.FullSubcategory) (X' H' : D)
    (hPG : K (op (G.obj P.obj.1.unop), G.obj P.obj.2))
    (cT : X ≅ TC.obj (L, P.obj.1.unop)) (cH : H ≅ HC.obj P)
    (cT' : X' ≅ TD.obj (L', P'.obj.1.unop)) (cH' : H' ≅ HD.obj P')
    (aL : T.obj L ≅ L') (aM : T.obj P.obj.1.unop ≅ P'.obj.1.unop)
    (aN : T.obj P.obj.2 ≅ P'.obj.2) (aX : T.obj X ≅ X') (aH : T.obj H ≅ H')
    (τ : G.obj (TC.obj (L, P.obj.1.unop)) ≅ TD.obj (G.obj L, G.obj P.obj.1.unop))
    (η : G.obj (HC.obj P) ≅ HD.obj ⟨(op (G.obj P.obj.1.unop), G.obj P.obj.2), hPG⟩)
    (st : (⟨(op (G.obj P.obj.1.unop), G.obj P.obj.2), hPG⟩ : K.FullSubcategory) ⟶ P')
    (hst₁ : (e.inv.app _ ≫ aM.hom) ≫ st.hom.1.unop = 𝟙 _)
    (hst₂ : st.hom.2 = e.inv.app _ ≫ aN.hom)
    (hcore : ∀ ψ : L ⟶ HC.obj P,
      G.map ((SC.transpose L P).symm ψ) =
        τ.hom ≫ (SD.transpose (G.obj L) ⟨(op (G.obj P.obj.1.unop), G.obj P.obj.2), hPG⟩).symm
          (G.map ψ ≫ η.hom))
    (htensor : aX.inv ≫ T.map cT.hom ≫ e.hom.app _ ≫ τ.hom ≫
      TD.map (Prod.mkHom (e.inv.app L ≫ aL.hom) (e.inv.app _ ≫ aM.hom)) = cT'.hom)
    (hhom : T.map cH.hom ≫ e.hom.app _ ≫ η.hom ≫ HD.map st = aH.hom ≫ cH'.hom)
    (φ : L ⟶ H) :
    aX.inv ≫ T.map (cT.hom ≫ (SC.transpose L P).symm (φ ≫ cH.hom)) ≫ aN.hom =
      cT'.hom ≫ (SD.transpose L' P').symm ((aL.inv ≫ T.map φ ≫ aH.hom) ≫ cH'.hom) := by
  have hT {Y Z : C} (x : Y ⟶ Z) : T.map x = e.hom.app Y ≫ G.map x ≫ e.inv.app Z :=
    (NatIso.naturality_2 e x).symm
  -- Move the Hom comparison across the transition.
  have hin : (aL.inv ≫ T.map φ ≫ aH.hom) ≫ cH'.hom =
      (aL.inv ≫ e.hom.app L) ≫ G.map (φ ≫ cH.hom) ≫ η.hom ≫ HD.map st := by
    rw [Category.assoc, Category.assoc, ← hhom, ← Functor.map_comp_assoc, hT]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  -- Absorb the parameter associator and the pair associator.
  have hpar := PodPartialClosed.symm_comp SD _ _ P' (aL.inv ≫ e.hom.app L)
    ((G.map (φ ≫ cH.hom) ≫ η.hom) ≫ HD.map st)
  have hpair := hSD (G.obj L) _ P' st (G.map (φ ≫ cH.hom) ≫ η.hom)
  have hcol : TD.map (Prod.mkHom (e.inv.app L ≫ aL.hom) (e.inv.app _ ≫ aM.hom)) ≫
      TD.map (Prod.mkHom (aL.inv ≫ e.hom.app L) (𝟙 _)) ≫
        TD.map (Prod.mkHom (𝟙 (G.obj L)) st.hom.1.unop) = 𝟙 _ := by
    rw [← TD.map_comp, ← TD.map_comp, ← TD.map_id]
    congr 1
    refine Prod.ext ?_ ?_
    · simp
    · simpa using hst₁
  rw [hin, ← Category.assoc (G.map (φ ≫ cH.hom)), hpar, hpair, ← htensor, hst₂,
    Functor.map_comp, hT ((SC.transpose L P).symm _), hcore]
  simp only [Category.assoc, reassoc_of% hcol]

end Abstract

section Tower
variable {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]

/-- For a family of bifunctors `U` on a stage system with comparisons `ρ` satisfying the
tower equation, the comparisons followed by the input associators, at two successive stages,
are related by the stage transition and the associators. -/
theorem stageComparison_endpoint_tower (S : StageSystem C) (U : ∀ i, C i × C i ⥤ C i)
    (ρ : ∀ {i j : I} (h : i ≤ j), U i ⋙ S.T h ≅ (S.T h).prod (S.T h) ⋙ U j)
    (hρ : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X Y : C i),
      (S.T h').map ((ρ h).hom.app (X, Y)) ≫ (ρ h').hom.app ((S.T h).obj X, (S.T h).obj Y) ≫
        (U k).map (X := ((S.T h').obj ((S.T h).obj X), (S.T h').obj ((S.T h).obj Y)))
          (Y := ((S.T (h.trans h')).obj X, (S.T (h.trans h')).obj Y))
          ((S.assoc h h').hom.app X, (S.assoc h h').hom.app Y) =
        (S.assoc h h').hom.app ((U i).obj (X, Y)) ≫ (ρ (h.trans h')).hom.app (X, Y))
    {iL iM i n p : I} (hL : iL ≤ i) (hM : iM ≤ i) (h : i ≤ n) (k : n ≤ p)
    (L : C iL) (M : C iM) :
    (S.assoc h k).inv.app _ ≫
        (S.T k).map ((ρ h).hom.app ((S.T hL).obj L, (S.T hM).obj M) ≫
          (U n).map (Prod.mkHom ((S.assoc hL h).hom.app L) ((S.assoc hM h).hom.app M))) ≫
        (ρ k).hom.app _ ≫
        (U p).map (Prod.mkHom ((S.assoc (hL.trans h) k).hom.app L)
          ((S.assoc (hM.trans h) k).hom.app M)) =
      (ρ (h.trans k)).hom.app ((S.T hL).obj L, (S.T hM).obj M) ≫
        (U p).map (Prod.mkHom ((S.assoc hL (h.trans k)).hom.app L)
          ((S.assoc hM (h.trans k)).hom.app M)) := by
  have hn := (ρ k).hom.naturality
    (Prod.mkHom ((S.assoc hL h).hom.app L) ((S.assoc hM h).hom.app M))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] at hn
  have hc : (U p).map (Prod.mkHom ((S.T k).map ((S.assoc hL h).hom.app L))
        ((S.T k).map ((S.assoc hM h).hom.app M))) ≫
      (U p).map (Prod.mkHom ((S.assoc (hL.trans h) k).hom.app L)
        ((S.assoc (hM.trans h) k).hom.app M)) =
      (U p).map (X := ((S.T k).obj ((S.T h).obj ((S.T hL).obj L)),
          (S.T k).obj ((S.T h).obj ((S.T hM).obj M))))
          (Y := ((S.T (h.trans k)).obj ((S.T hL).obj L),
            (S.T (h.trans k)).obj ((S.T hM).obj M)))
          ((S.assoc h k).hom.app _, (S.assoc h k).hom.app _) ≫
        (U p).map (Prod.mkHom ((S.assoc hL (h.trans k)).hom.app L)
          ((S.assoc hM (h.trans k)).hom.app M)) := by
    rw [← (U p).map_comp, ← (U p).map_comp]
    congr 1
    exact Prod.ext (S.cocycle hL h k L) (S.cocycle hM h k M)
  rw [Functor.map_comp, Category.assoc, reassoc_of% hn]
  rw [hc]
  rw [reassoc_of% (hρ h k ((S.T hL).obj L) ((S.T hM).obj M)), Iso.inv_hom_id_app_assoc]


/-- The endpoint tower equation of `stageComparison_endpoint_tower`, for given endpoint
comparisons `cT`, `cT'`, with the stage comparison `ρ k` written through a functor `G`
isomorphic to the transition and a comparison `τ` for `G`. -/
theorem stageComparison_scalar_tower (S : StageSystem C) (U : ∀ i, C i × C i ⥤ C i)
    (ρ : ∀ {i j : I} (h : i ≤ j), U i ⋙ S.T h ≅ (S.T h).prod (S.T h) ⋙ U j)
    (hρ : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X Y : C i),
      (S.T h').map ((ρ h).hom.app (X, Y)) ≫ (ρ h').hom.app ((S.T h).obj X, (S.T h).obj Y) ≫
        (U k).map (X := ((S.T h').obj ((S.T h).obj X), (S.T h').obj ((S.T h).obj Y)))
          (Y := ((S.T (h.trans h')).obj X, (S.T (h.trans h')).obj Y))
          ((S.assoc h h').hom.app X, (S.assoc h h').hom.app Y) =
        (S.assoc h h').hom.app ((U i).obj (X, Y)) ≫ (ρ (h.trans h')).hom.app (X, Y))
    {iL iM i n p : I} (hL : iL ≤ i) (hM : iM ≤ i) (h : i ≤ n) (k : n ≤ p)
    (L : C iL) (M : C iM)
    (cT : (S.T h).obj ((U i).obj ((S.T hL).obj L, (S.T hM).obj M)) ≅
      (U n).obj ((S.T (hL.trans h)).obj L, (S.T (hM.trans h)).obj M))
    (hcT : cT.hom = (ρ h).hom.app ((S.T hL).obj L, (S.T hM).obj M) ≫
      (U n).map (Prod.mkHom ((S.assoc hL h).hom.app L) ((S.assoc hM h).hom.app M)))
    (cT' : (S.T (h.trans k)).obj ((U i).obj ((S.T hL).obj L, (S.T hM).obj M)) ≅
      (U p).obj ((S.T (hL.trans (h.trans k))).obj L, (S.T (hM.trans (h.trans k))).obj M))
    (hcT' : cT'.hom = (ρ (h.trans k)).hom.app ((S.T hL).obj L, (S.T hM).obj M) ≫
      (U p).map (Prod.mkHom ((S.assoc hL (h.trans k)).hom.app L)
        ((S.assoc hM (h.trans k)).hom.app M)))
    (G : C n ⥤ C p) (e : S.T k ≅ G) (τ : U n ⋙ G ≅ G.prod G ⋙ U p)
    (hρk : ∀ Y Z : C n, (ρ k).hom.app (Y, Z) =
      e.hom.app _ ≫ τ.hom.app (Y, Z) ≫ (U p).map (Prod.mkHom (e.inv.app Y) (e.inv.app Z))) :
    ((S.assoc h k).app _).inv ≫ (S.T k).map cT.hom ≫ e.hom.app _ ≫
        (τ.app ((S.T (hL.trans h)).obj L, (S.T (hM.trans h)).obj M)).hom ≫
        (U p).map (Prod.mkHom (e.inv.app _ ≫ ((S.assoc (hL.trans h) k).app L).hom)
          (e.inv.app _ ≫ ((S.assoc (hM.trans h) k).app M).hom)) = cT'.hom := by
  have hsplit : (U p).map (Prod.mkHom (e.inv.app _ ≫ ((S.assoc (hL.trans h) k).app L).hom)
        (e.inv.app _ ≫ ((S.assoc (hM.trans h) k).app M).hom)) =
      (U p).map (Prod.mkHom (e.inv.app ((S.T (hL.trans h)).obj L))
        (e.inv.app ((S.T (hM.trans h)).obj M))) ≫
      (U p).map (Prod.mkHom ((S.assoc (hL.trans h) k).hom.app L)
        ((S.assoc (hM.trans h) k).hom.app M)) := by
    rw [← (U p).map_comp]
    rfl
  rw [hsplit, Iso.app_hom, ← Category.assoc (τ.hom.app _), ← Category.assoc (e.hom.app _),
    ← hρk, hcT, hcT', Iso.app_inv]
  exact stageComparison_endpoint_tower S U ρ hρ hL hM h k L M

end Tower

end WeilConjectures
