/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TruncationTower
public import WeilConjectures.CategoryTheory.Triangulated.TriangleTowerMap

/-!
# The truncation exact couple of a triangulated functor

Let `F : D⁺(C) ⥤ D⁺(D)` be a triangulated functor and `K` an object of `D⁺(C)`. Applying `F`
to the tower of truncation triangles
`τ_{≤ q-1} K ⟶ τ_{≤ q} K ⟶ H^q(K)[-q] ⟶ (τ_{≤ q-1} K)⟦1⟧` of `K`
(`DerivedCategory.Plus.truncLETower`) and taking cohomology gives the exact couple
`DerivedCategory.Plus.truncationCouple F K` with
```
  D^{p,q} = H^{p+q}(F(τ_{≤ q} K)),     E^{p,q} = H^{p+q}(F(H^q(K)[-q])).
```
A natural transformation `τ : F₁ ⟶ F₂` of triangulated functors which commutes with the shifts
induces a morphism of exact couples `DerivedCategory.Plus.truncationCoupleMap τ K`, with
components `H^{p+q}(τ_{τ_{≤ q} K})` and `H^{p+q}(τ_{H^q(K)[-q]})`. Under the identifications
`E^{p,q} ≅ H^p(F(H^q(K)))` (`DerivedCategory.Plus.truncationCoupleEIso`, given by the shift
isomorphisms of `F` and of the cohomology functors) its component on `E^{p,q}` is
`H^p(τ_{H^q(K)})` (`DerivedCategory.Plus.truncationCoupleMap_hE`).
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory.Plus

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Abelian D] [HasDerivedCategory D]

section

variable (F : Plus C ⥤ Plus D) [F.CommShift ℤ] [F.IsTriangulated] (K : Plus C)

/-- The truncation exact couple of a triangulated functor `F : D⁺(C) ⥤ D⁺(D)` at `K`:
`D^{p,q} = H^{p+q}(F(τ_{≤ q} K))` and `E^{p,q} = H^{p+q}(F(H^q(K)[-q]))`, with `α`, `g` induced
by the maps of the truncation triangles and `f` the connecting morphism of the long exact
cohomology sequence of the image under `F` of the truncation triangle. -/
noncomputable def truncationCouple : ExactCouple D 0 :=
  ((truncLETower K).map F).exactCouple (homologyFunctor D 0)

lemma truncationCouple_D (p q : ℤ) :
    (truncationCouple F K).D p q =
      ((homologyFunctor D 0).shift (p + q)).obj (F.obj ((truncLE C q).obj K)) :=
  rfl

lemma truncationCouple_E (p q : ℤ) :
    (truncationCouple F K).E p q =
      ((homologyFunctor D 0).shift (p + q)).obj (F.obj ((homologySingleFunctor C q).obj K)) :=
  rfl

/-- The identification `E^{p,q} = H^{p+q}(F(H^q(K)[-q])) ≅ H^p(F(H^q(K)))` of the `E`-terms
of the truncation couple, given by the shift isomorphisms of `F` and of the cohomology
functors. -/
noncomputable def truncationCoupleEIso (p q : ℤ) :
    (truncationCouple F K).E p q ≅
      ((homologyFunctor D 0).shift p).obj
        (F.obj ((singleFunctor C 0).obj ((homologyFunctor C q).obj K))) :=
  ((homologyFunctor D 0).shift (p + q)).mapIso
      (F.mapIso ((homologySingleFunctorIso C q).app K ≪≫
        ((singleFunctors C).shiftIso (-q) q 0 (by lia)).symm.app _)) ≪≫
    ((homologyFunctor D 0).shift (p + q)).mapIso ((F.commShiftIso (-q)).app _) ≪≫
    ((homologyFunctor D 0).shiftIso (-q) (p + q) p (by lia)).app _

end

section

variable {F₁ F₂ : Plus C ⥤ Plus D} [F₁.CommShift ℤ] [F₁.IsTriangulated] [F₂.CommShift ℤ]
  [F₂.IsTriangulated] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (K : Plus C)

/-- The morphism of truncation exact couples induced by a natural transformation of
triangulated functors which commutes with the shifts. -/
noncomputable def truncationCoupleMap : truncationCouple F₁ K ⟶ truncationCouple F₂ K :=
  ((truncLETower K).mapHom τ).exactCoupleMap _

@[simp]
lemma truncationCoupleMap_hD (p q : ℤ) :
    (truncationCoupleMap τ K).hD p q =
      ((homologyFunctor D 0).shift (p + q)).map (τ.app ((truncLE C q).obj K)) :=
  rfl

@[simp]
lemma truncationCoupleMap_hE (p q : ℤ) :
    (truncationCoupleMap τ K).hE p q =
      ((homologyFunctor D 0).shift (p + q)).map (τ.app ((homologySingleFunctor C q).obj K)) :=
  rfl

omit [F₁.IsTriangulated] [F₂.IsTriangulated] in
lemma shift_map_app_comp_shiftIso {G Y : Plus C} (a n m : ℤ) (h : a + n = m) (c : G ⟶ Y⟦a⟧) :
    ((homologyFunctor D 0).shift n).map (τ.app G) ≫
        ((homologyFunctor D 0).shift n).map (F₂.map c) ≫
        ((homologyFunctor D 0).shift n).map ((F₂.commShiftIso a).hom.app Y) ≫
        ((homologyFunctor D 0).shiftIso a n m h).hom.app (F₂.obj Y) =
      ((homologyFunctor D 0).shift n).map (F₁.map c) ≫
        ((homologyFunctor D 0).shift n).map ((F₁.commShiftIso a).hom.app Y) ≫
        ((homologyFunctor D 0).shiftIso a n m h).hom.app (F₁.obj Y) ≫
        ((homologyFunctor D 0).shift m).map (τ.app Y) := by
  have key : τ.app G ≫ F₂.map c ≫ (F₂.commShiftIso a).hom.app Y =
      F₁.map c ≫ (F₁.commShiftIso a).hom.app Y ≫ (τ.app Y)⟦a⟧' := by
    rw [NatTrans.shift_app_comm, τ.naturality_assoc]
  have h₂ := ((homologyFunctor D 0).shiftIso a n m h).hom.naturality (τ.app Y)
  simp only [Functor.comp_map] at h₂
  rw [← h₂]
  simp only [← Functor.map_comp_assoc, key]

/-- Under the identifications `E^{p,q} ≅ H^p(Fᵢ(H^q(K)))`, the component of the morphism of
truncation couples on `E^{p,q}` is `H^p(τ_{H^q(K)})`. -/
@[reassoc]
lemma truncationCoupleMap_hE_comp_truncationCoupleEIso_hom (p q : ℤ) :
    (truncationCoupleMap τ K).hE p q ≫ (truncationCoupleEIso F₂ K p q).hom =
      (truncationCoupleEIso F₁ K p q).hom ≫ ((homologyFunctor D 0).shift p).map
        (τ.app ((singleFunctor C 0).obj ((homologyFunctor C q).obj K))) := by
  simp only [truncationCoupleEIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, assoc]
  exact shift_map_app_comp_shiftIso τ (-q) (p + q) p _ _
/-- Under the identifications `E^{p,q} ≅ H^p(Fᵢ(H^q(K)))`, the component of the morphism of
truncation couples on `E^{p,q}` is `H^p(τ_{H^q(K)})`. -/
lemma truncationCoupleMap_hE_eq (p q : ℤ) :
    (truncationCoupleMap τ K).hE p q =
      (truncationCoupleEIso F₁ K p q).hom ≫ ((homologyFunctor D 0).shift p).map
        (τ.app ((singleFunctor C 0).obj ((homologyFunctor C q).obj K))) ≫
          (truncationCoupleEIso F₂ K p q).inv := by
  rw [← truncationCoupleMap_hE_comp_truncationCoupleEIso_hom_assoc, Iso.hom_inv_id, comp_id]

end

end DerivedCategory.Plus
