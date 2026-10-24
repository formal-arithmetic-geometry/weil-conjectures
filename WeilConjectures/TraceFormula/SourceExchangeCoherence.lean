/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleSquareCoherence
public import WeilConjectures.TraceFormula.ProperKunneth
public import WeilConjectures.TraceFormula.ShriekTrace

/-!

# Coherence of composition isomorphisms around a pushforward square

For morphisms `g : C ⟶ D`, `b : D ⟶ W`, `c : C ⟶ V`, `q : V ⟶ W`, `p : W ⟶ Y`, `p' : V ⟶ X` and
`f : X ⟶ Y` with `g ≫ b = c ≫ q` and `q ≫ p = p' ≫ f`, the two identifications of
`Rg_! ⋙ Rb_! ⋙ Rp_!` with `Rc_! ⋙ Rp'_! ⋙ Rf_!` built from the composition isomorphisms agree
(`ProEtale.CondensedRing.lowerShriekComp_pushforwardSquare`), and similarly for the derived
pullbacks (`ProEtale.CondensedRing.upperStarComp_pushforwardSquare`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

@[reassoc]
lemma MonoidalCategory.rightUnitor_inv_comp_whiskerRight_comp_hom {C : Type*} [Category C]
    [MonoidalCategory C] {X Y : C} (f : X ⟶ Y) : (ρ_ X).inv ≫ f ▷ 𝟙_ C ≫ (ρ_ Y).hom = f := by
  simp

@[reassoc]
lemma Functor.map_hom_app_comp_map_inv_app {B C D : Type*} [Category B] [Category C]
    [Category D] (H : C ⥤ D) {F G : B ⥤ C} (e : F ≅ G) (X : B) :
    H.map (e.hom.app X) ≫ H.map (e.inv.app X) = 𝟙 _ := by
  rw [← H.map_comp, e.hom_inv_id_app, H.map_id]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {C D V W X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

@[reassoc]
lemma lowerShriek_map_eqToHom_comp_lowerShriekComp_inv_app' {u u' : C ⟶ D} (h : u = u')
    (z : D ⟶ W) (M : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek _ ℓ z).map (eqToHom (by rw [h])) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ u' z).inv.app M =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ u z).inv.app M ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The composition isomorphisms of the compactly supported direct images around a pushforward
square agree. -/
@[reassoc]
lemma lowerShriekComp_pushforwardSquare (g : C ⟶ D) (b : D ⟶ W) (c : C ⟶ V) (q : V ⟶ W)
    (p : W ⟶ Y) (p' : V ⟶ X) (f : X ⟶ Y) (hgq : g ≫ b = c ≫ q) (hq : q ≫ p = p' ≫ f)
    (w : g ≫ b ≫ p = (c ≫ p') ≫ f) (M : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b p).inv.app
        ((boundedConstructibleLowerShriek _ ℓ g).obj M) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (b ≫ p)).inv.app M ≫
      eqToHom (by rw [w]) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (c ≫ p') f).hom.app M =
    (boundedConstructibleLowerShriek _ ℓ p).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app M) ≫
      (boundedConstructibleLowerShriek _ ℓ p).map (eqToHom (by rw [hgq])) ≫
      (boundedConstructibleLowerShriek _ ℓ p).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom.app M) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ hq).hom.app
        ((boundedConstructibleLowerShriek _ ℓ c).obj M) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c p').inv.app M) := by
  have h₁ := lowerShriek_map_lowerShriekComp_inv_app_comp_inv_app ℓ g b p M
  have h₁' : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b p).inv.app
        ((boundedConstructibleLowerShriek _ ℓ g).obj M) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (b ≫ p)).inv.app M =
      (boundedConstructibleLowerShriek _ ℓ p).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app M) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (g ≫ b) p).inv.app M ≫
        eqToHom (by rw [Category.assoc]) := by
    rw [reassoc_of% h₁]
    simp
  rw [reassoc_of% h₁']
  refine whisker_eq _ ?_
  simp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Functor.comp_obj,
    Category.assoc]
  rw [lowerShriek_map_lowerShriekComp_hom_app_comp_inv_app_assoc ℓ c q p M,
    lowerShriek_map_eqToHom_comp_lowerShriekComp_inv_app'_assoc ℓ hgq p M]
  refine whisker_eq _ ?_
  rw [lowerShriekComp_hom_app_comp_eqToHom_assoc ℓ hq c M,
    lowerShriekComp_hom_app_comp_hom_app_assoc]
  simp

section Pullback

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The composition isomorphisms with a common first map are compatible with the casts along
`r = r'`. -/
@[reassoc]
lemma boundedConstructibleUpperStarComp_hom_app_map_eqToHom {r r' : V ⟶ W} (h : r = r')
    (a : C ⟶ V) (A : Dᵇc(W.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ a r).hom.app A ≫
      (boundedConstructibleUpperStar Λ ℓ a).map
        (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj A) h)) =
    eqToHom (by rw [h]) ≫ (boundedConstructibleUpperStarComp Λ ℓ a r').hom.app A := by
  subst h
  simp

/-- The composition isomorphisms of the derived pullbacks around a pushforward square agree. -/
lemma boundedConstructibleUpperStarComp_pushforwardSquare (g : C ⟶ D) (b : D ⟶ W) (c : C ⟶ V)
    (q : V ⟶ W) (p : W ⟶ Y) (p' : V ⟶ X) (f : X ⟶ Y) (hgq : g ≫ b = c ≫ q)
    (hq : q ≫ p = p' ≫ f) (w : g ≫ b ≫ p = (c ≫ p') ≫ f) (N : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStar Λ ℓ g).map
        ((boundedConstructibleUpperStarComp Λ ℓ b p).inv.app N) ≫
      (boundedConstructibleUpperStarComp Λ ℓ g (b ≫ p)).inv.app N ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj N) w) ≫
      (boundedConstructibleUpperStarComp Λ ℓ (c ≫ p') f).hom.app N =
    (boundedConstructibleUpperStarComp Λ ℓ g b).inv.app ((boundedConstructibleUpperStar Λ ℓ p).obj N) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ p).obj N)) hgq) ≫
      (boundedConstructibleUpperStarComp Λ ℓ c q).hom.app ((boundedConstructibleUpperStar Λ ℓ p).obj N) ≫
      (boundedConstructibleUpperStar Λ ℓ c).map
        ((boundedConstructibleUpperStarComp Λ ℓ q p).inv.app N ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj N) hq) ≫
          (boundedConstructibleUpperStarComp Λ ℓ p' f).hom.app N) ≫
      (boundedConstructibleUpperStarComp Λ ℓ c p').inv.app ((boundedConstructibleUpperStar Λ ℓ f).obj N) := by
  have e₁ := boundedConstructibleUpperStarComp_hom_app_map_inv_app Λ ℓ c q p N
  have e₂ := boundedConstructibleUpperStar_map_hom_app_comp_inv_app Λ ℓ c p' f N
  have e₃ := boundedConstructibleUpperStarComp_hom_app_map_eqToHom ℓ Λ hq c N
  have e₅ := eqToHom_comp_boundedConstructibleUpperStarComp_inv_app Λ ℓ hgq p N
  have e₆ := boundedConstructibleUpperStarComp_inv_app_comp_inv_app' Λ ℓ g b p N
  simp only [Functor.map_comp, Category.assoc]
  rewrite [reassoc_of% e₁, reassoc_of% e₅, reassoc_of% e₆, reassoc_of% e₃]
  simp only [e₂, Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc]

end Pullback
section Coefficient

@[reassoc]
lemma lowerShriekComp_inv_app_naturality (x : C ⟶ D) (y : D ⟶ W)
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek _ ℓ y).map ((boundedConstructibleLowerShriek _ ℓ x).map φ) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app N =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M ≫
        (boundedConstructibleLowerShriek _ ℓ (x ≫ y)).map φ :=
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.naturality φ

@[reassoc]
lemma lowerShriekComp_hom_app_naturality (x : C ⟶ D) (y : D ⟶ W)
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek _ ℓ (x ≫ y)).map φ ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app N =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app M ≫
        (boundedConstructibleLowerShriek _ ℓ y).map ((boundedConstructibleLowerShriek _ ℓ x).map φ) :=
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.naturality φ

@[reassoc]
lemma lowerShriek_map_comp_eqToHom' {u u' : C ⟶ D} (h : u = u')
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek _ ℓ u).map φ ≫
        eqToHom (by rw [h] : (boundedConstructibleLowerShriek _ ℓ u).obj N =
          (boundedConstructibleLowerShriek _ ℓ u').obj N) =
      eqToHom (by rw [h]) ≫ (boundedConstructibleLowerShriek _ ℓ u').map φ := by
  subst h
  simp

@[reassoc]
lemma lowerShriekSquareIso_hom_app_naturality {g' : C ⟶ D} {f₀ : D ⟶ W} {f' : C ⟶ X}
    {g₀ : X ⟶ W} (w : g' ≫ f₀ = f' ≫ g₀) {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek _ ℓ f₀).map ((boundedConstructibleLowerShriek _ ℓ g').map φ) ≫
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app N =
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app M ≫
        (boundedConstructibleLowerShriek _ ℓ g₀).map ((boundedConstructibleLowerShriek _ ℓ f').map φ) :=
  (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.naturality φ

@[reassoc]
lemma map_lowerShriekComp_inv_app_naturality (x : C ⟶ D) (y : D ⟶ W)
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) {Z : Type*} [Category Z]
    (F : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) :
    F.map ((boundedConstructibleLowerShriek _ ℓ y).map
        ((boundedConstructibleLowerShriek _ ℓ x).map φ)) ≫
        F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app N) =
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M) ≫
        F.map ((boundedConstructibleLowerShriek _ ℓ (x ≫ y)).map φ) := by
  simp only [← F.map_comp, lowerShriekComp_inv_app_naturality]

@[reassoc]
lemma map_lowerShriekComp_hom_app_naturality (x : C ⟶ D) (y : D ⟶ W)
    {M N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) {Z : Type*} [Category Z]
    (F : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) :
    F.map ((boundedConstructibleLowerShriek _ ℓ (x ≫ y)).map φ) ≫
        F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app N) =
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app M) ≫
        F.map ((boundedConstructibleLowerShriek _ ℓ y).map
          ((boundedConstructibleLowerShriek _ ℓ x).map φ)) := by
  simp only [← F.map_comp, lowerShriekComp_hom_app_naturality]

/-- Moving maps past a cast `Ru_! = R(c ≫ q)_!` and the composition isomorphism of `c ≫ q`. -/
lemma map_lowerShriek_map_comp_eqToHom_comp_lowerShriekComp_hom_app {u : C ⟶ W} (c : C ⟶ V)
    (q : V ⟶ W) (h : u = c ≫ q) {M M' N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (A : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (T : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (φ₁ : M ⟶ M') (φ₂ : M' ⟶ (boundedConstructibleUpperStar _ ℓ u).obj A ⊗ T)
    (ψ : (boundedConstructibleUpperStar _ ℓ (c ≫ q)).obj A ⊗ T ⟶ N) {Z : Type*} [Category Z]
    (F : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) {E : Z}
    (k : F.obj ((boundedConstructibleLowerShriek _ ℓ q).obj
      ((boundedConstructibleLowerShriek _ ℓ c).obj N)) ⟶ E) :
    F.map ((boundedConstructibleLowerShriek _ ℓ u).map φ₁) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ u).map φ₂) ≫
      F.map (eqToHom (by rw [h] : (boundedConstructibleLowerShriek _ ℓ u).obj
          ((boundedConstructibleUpperStar _ ℓ u).obj A ⊗ T) =
        (boundedConstructibleLowerShriek _ ℓ (c ≫ q)).obj
          ((boundedConstructibleUpperStar _ ℓ (c ≫ q)).obj A ⊗ T))) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ (c ≫ q)).map ψ) ≫
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom.app N) ≫ k =
    F.map (eqToHom (by rw [h] : (boundedConstructibleLowerShriek _ ℓ u).obj M =
        (boundedConstructibleLowerShriek _ ℓ (c ≫ q)).obj M)) ≫
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom.app M) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ q).map ((boundedConstructibleLowerShriek _ ℓ c).map
        (φ₁ ≫ φ₂ ≫ eqToHom (by rw [h]) ≫ ψ))) ≫ k := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp,
    Category.assoc, map_lowerShriekComp_hom_app_naturality_assoc]

/-- Moving four maps past the inverse composition isomorphism, under a functor. -/
lemma map_lowerShriek_map₄_comp_lowerShriekComp_inv_app (x : C ⟶ D) (y : D ⟶ W)
    {M₀ M₁ M₂ M₃ M₄ : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a₁ : M₀ ⟶ M₁) (a₂ : M₁ ⟶ M₂)
    (a₃ : M₂ ⟶ M₃) (a₄ : M₃ ⟶ M₄) {Z : Type*} [Category Z]
    (F : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) :
    F.map ((boundedConstructibleLowerShriek _ ℓ y).map ((boundedConstructibleLowerShriek _ ℓ x).map a₁)) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ y).map ((boundedConstructibleLowerShriek _ ℓ x).map a₂)) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ y).map ((boundedConstructibleLowerShriek _ ℓ x).map a₃)) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ y).map ((boundedConstructibleLowerShriek _ ℓ x).map a₄)) ≫
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M₄) =
    F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M₀) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ (x ≫ y)).map (a₁ ≫ a₂ ≫ a₃ ≫ a₄)) := by
  simp only [Functor.map_comp, Category.assoc, map_lowerShriekComp_inv_app_naturality_assoc,
    map_lowerShriekComp_inv_app_naturality]

lemma eqToHom_upperStar_tensor {u u' : C ⟶ D} (h : u = u')
    (A : Dᵇc(D.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (T : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    eqToHom (by rw [h] : (boundedConstructibleUpperStar _ ℓ u).obj A ⊗ T =
        (boundedConstructibleUpperStar _ ℓ u').obj A ⊗ T) =
      eqToHom (by rw [h] : (boundedConstructibleUpperStar _ ℓ u).obj A =
        (boundedConstructibleUpperStar _ ℓ u').obj A) ▷ T := by
  subst h
  simp

/-- Moving a map past the unit of `Lg^* ⊣ Rg_*` and `Rg_* ≅ Rg_!`. -/
lemma map_unit_comp_lowerShriekIsoLowerStar_inv (g : C ⟶ D) [IsProper g.left]
    {A B : Dᵇc(D.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (u : A ⟶ B)
    {E : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (y : (boundedConstructibleUpperStar _ ℓ g).obj B ⟶ E) {Z : Type*} [Category Z]
    (F : Dᵇc(D.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Z) {T : Z}
    (k : F.obj ((boundedConstructibleLowerShriek _ ℓ g).obj E) ⟶ T) :
    F.map u ≫
      F.map ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app B ≫
        (boundedConstructibleLowerStar _ ℓ g).map y) ≫
      F.map ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app E) ≫ k =
    F.map ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app A) ≫
      F.map ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj A)) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ g).map
        ((boundedConstructibleUpperStar _ ℓ g).map u ≫ y)) ≫ k := by
  have h₁ := (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.naturality u
  have h₂ := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.naturality
    ((boundedConstructibleUpperStar _ ℓ g).map u ≫ y)
  simp only [Functor.comp_map, Functor.id_map] at h₁ h₂
  simp only [← F.map_comp_assoc, Category.assoc]
  rewrite [reassoc_of% h₁, ← (boundedConstructibleLowerStar _ ℓ g).map_comp_assoc, h₂]
  simp only [Functor.map_comp, Category.assoc]

set_option maxHeartbeats 4000000 in
-- the compactly supported direct images are unfolded in the defeq checks
/-- The coherence part of the class of the coefficient pushforward: for `g ≫ b = c ≫ q`,
`q ≫ p₁ = p₁' ≫ f`, `q ≫ p₂ = p₂' ≫ f` with `g`, `f` proper, the two maps
`Rp₁_! Rb_! Lb^* Lp₂^* Rf_* K ⟶ Rf_! Rc₁_! Lc₂^* K` agree. -/
theorem lowerShriek_pushforwardCoeff_coherence (g : C ⟶ D) [IsProper g.left] (b : D ⟶ W)
    (c : C ⟶ V) (q : V ⟶ W) (f : X ⟶ Y) [IsProper f.left] (p₁ p₂ : W ⟶ Y) (p₁' p₂' : V ⟶ X)
    {b₁ b₂ : D ⟶ Y} {c₁ c₂ : C ⟶ X} (hb₁ : b ≫ p₁ = b₁) (hb₂ : b ≫ p₂ = b₂)
    (hc₁ : c ≫ p₁' = c₁) (hc₂ : c ≫ p₂' = c₂) (hgq : g ≫ b = c ≫ q) (hq₁ : q ≫ p₁ = p₁' ≫ f)
    (hq₂ : q ≫ p₂ = p₂' ≫ f) (w₁ : g ≫ b₁ = c₁ ≫ f) (w₂ : g ≫ b₂ = c₂ ≫ f)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek _ ℓ p₁).map ((boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleUpperStarComp _ ℓ b p₂).inv.app
          ((boundedConstructibleLowerStar _ ℓ f).obj K))) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b p₁).inv.app
        ((boundedConstructibleUpperStar _ ℓ (b ≫ p₂)).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj K)) ≫
      (boundedConstructibleLowerShriek _ ℓ (b ≫ p₁)).map (eqToHom (by rw [hb₂])) ≫
      eqToHom (by rw [hb₁] : (boundedConstructibleLowerShriek _ ℓ (b ≫ p₁)).obj
          ((boundedConstructibleUpperStar _ ℓ b₂).obj ((boundedConstructibleLowerStar _ ℓ f).obj K)) =
        (boundedConstructibleLowerShriek _ ℓ b₁).obj
          ((boundedConstructibleUpperStar _ ℓ b₂).obj ((boundedConstructibleLowerStar _ ℓ f).obj K))) ≫
      (boundedConstructibleLowerShriek _ ℓ b₁).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app
            ((boundedConstructibleUpperStar _ ℓ b₂).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj K)) ≫
          (boundedConstructibleLowerStar _ ℓ g).map
            ((boundedConstructibleUpperStarComp _ ℓ g b₂).inv.app
                ((boundedConstructibleLowerStar _ ℓ f).obj K) ≫
              eqToHom (by rw [w₂]) ≫
              (boundedConstructibleUpperStarComp _ ℓ c₂ f).hom.app
                ((boundedConstructibleLowerStar _ ℓ f).obj K) ≫
              (boundedConstructibleUpperStar _ ℓ c₂).map
                ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app K))) ≫
      (boundedConstructibleLowerShriek _ ℓ b₁).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
          ((boundedConstructibleUpperStar _ ℓ c₂).obj K)) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b₁).inv.app
        ((boundedConstructibleUpperStar _ ℓ c₂).obj K) ≫
      eqToHom (by rw [w₁]) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c₁ f).hom.app
        ((boundedConstructibleUpperStar _ ℓ c₂).obj K) =
    (boundedConstructibleLowerShriek _ ℓ p₁).map ((boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app
          ((boundedConstructibleUpperStar _ ℓ b).obj ((boundedConstructibleUpperStar _ ℓ p₂).obj
            ((boundedConstructibleLowerStar _ ℓ f).obj K))))) ≫
      (boundedConstructibleLowerShriek _ ℓ p₁).map ((boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
          ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj K)))))) ≫
      (boundedConstructibleLowerShriek _ ℓ p₁).map ((boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleLowerShriek _ ℓ g).map
          (ρ_ ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj K))))).inv)) ≫
      (boundedConstructibleLowerShriek _ ℓ p₁).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app
          ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj K))) ⊗ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriek _ ℓ p₁).map ((boundedConstructibleLowerShriek _ ℓ (g ≫ b)).map
        ((boundedConstructibleUpperStarComp _ ℓ g b).inv.app ((boundedConstructibleUpperStar _ ℓ p₂).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj K)) ▷ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriek _ ℓ p₁).map (eqToHom (by rw [hgq])) ≫
      (boundedConstructibleLowerShriek _ ℓ p₁).map ((boundedConstructibleLowerShriek _ ℓ (c ≫ q)).map
        ((boundedConstructibleUpperStarComp _ ℓ c q).hom.app ((boundedConstructibleUpperStar _ ℓ p₂).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj K)) ▷ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriek _ ℓ p₁).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom.app
          ((boundedConstructibleUpperStar _ ℓ c).obj ((boundedConstructibleUpperStar _ ℓ q).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj K))) ⊗ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ hq₁).hom.app
        ((boundedConstructibleLowerShriek _ ℓ c).obj
          ((boundedConstructibleUpperStar _ ℓ c).obj ((boundedConstructibleUpperStar _ ℓ q).obj
            ((boundedConstructibleUpperStar _ ℓ p₂).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj K))) ⊗ 𝟙_ _)) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map ((boundedConstructibleLowerShriek _ ℓ p₁').map
        ((boundedConstructibleLowerShriek _ ℓ c).map
          ((boundedConstructibleUpperStar _ ℓ c).map (prodUpperStarCounit ℓ hq₂ K) ▷ 𝟙_ _))) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map ((boundedConstructibleLowerShriek _ ℓ p₁').map
        ((boundedConstructibleLowerShriek _ ℓ c).map
          (ρ_ ((boundedConstructibleUpperStar _ ℓ c).obj
            ((boundedConstructibleUpperStar _ ℓ p₂').obj K))).hom)) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map ((boundedConstructibleLowerShriek _ ℓ p₁').map
        ((boundedConstructibleLowerShriek _ ℓ c).map
          ((boundedConstructibleUpperStarComp _ ℓ c p₂').inv.app K))) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c p₁').inv.app
          ((boundedConstructibleUpperStar _ ℓ (c ≫ p₂')).obj K)) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map
        ((boundedConstructibleLowerShriek _ ℓ (c ≫ p₁')).map (eqToHom (by rw [hc₂]))) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map (eqToHom (by rw [hc₁] :
        (boundedConstructibleLowerShriek _ ℓ (c ≫ p₁')).obj ((boundedConstructibleUpperStar _ ℓ c₂).obj K) =
          (boundedConstructibleLowerShriek _ ℓ c₁).obj ((boundedConstructibleUpperStar _ ℓ c₂).obj K))) := by
  subst hb₁ hb₂ hc₁ hc₂
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rewrite [lowerShriekComp_inv_app_naturality_assoc ℓ b p₁
    ((boundedConstructibleUpperStarComp _ ℓ b p₂).inv.app ((boundedConstructibleLowerStar _ ℓ f).obj K))]
  rewrite [map_unit_comp_lowerShriekIsoLowerStar_inv ℓ g
    (E := (boundedConstructibleUpperStar _ ℓ (c ≫ p₂')).obj K)
    ((boundedConstructibleUpperStarComp _ ℓ b p₂).inv.app ((boundedConstructibleLowerStar _ ℓ f).obj K))
    ((boundedConstructibleUpperStarComp _ ℓ g (b ≫ p₂)).inv.app
        ((boundedConstructibleLowerStar _ ℓ f).obj K) ≫
      eqToHom (by rw [w₂]) ≫
      (boundedConstructibleUpperStarComp _ ℓ (c ≫ p₂') f).hom.app
        ((boundedConstructibleLowerStar _ ℓ f).obj K) ≫
      (boundedConstructibleUpperStar _ ℓ (c ≫ p₂')).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app K))
    (boundedConstructibleLowerShriek _ ℓ (b ≫ p₁))]
  dsimp only [Functor.comp_obj]
  rewrite [lowerShriekComp_inv_app_naturality_assoc ℓ g (b ≫ p₁), lowerShriek_map_comp_eqToHom'_assoc ℓ w₁,
    lowerShriekComp_hom_app_naturality ℓ (c ≫ p₁') f]
  dsimp only [Functor.comp_obj]
  rewrite [← lowerShriekComp_inv_app_naturality_assoc ℓ b p₁
      (M := (boundedConstructibleUpperStar _ ℓ b).obj ((boundedConstructibleUpperStar _ ℓ p₂).obj
        ((boundedConstructibleLowerStar _ ℓ f).obj K)))
      ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app
        ((boundedConstructibleUpperStar _ ℓ b).obj ((boundedConstructibleUpperStar _ ℓ p₂).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj K))))]
  dsimp only [Functor.comp_obj]
  rewrite [← lowerShriekComp_inv_app_naturality_assoc ℓ b p₁
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleUpperStar _ ℓ b).obj
          ((boundedConstructibleUpperStar _ ℓ p₂).obj ((boundedConstructibleLowerStar _ ℓ f).obj K)))))]
  rewrite [lowerShriekComp_pushforwardSquare_assoc ℓ g b c q p₁ p₁' f hgq hq₁ w₁]
  refine whisker_eq _ (whisker_eq _ ?_)
  rewrite [map_lowerShriekComp_inv_app_naturality_assoc ℓ g b _ (boundedConstructibleLowerShriek _ ℓ p₁)]
  rewrite [map_lowerShriek_map_comp_eqToHom_comp_lowerShriekComp_hom_app ℓ c q hgq]
  rewrite [lowerShriekSquareIso_hom_app_naturality_assoc ℓ hq₁]
  rewrite [map_lowerShriek_map₄_comp_lowerShriekComp_inv_app ℓ c p₁']
  refine whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ ?_))))
  refine congrArg (fun t ↦ (boundedConstructibleLowerShriek _ ℓ f).map
    ((boundedConstructibleLowerShriek _ ℓ (c ≫ p₁')).map t)) ?_
  have hs := boundedConstructibleUpperStarComp_pushforwardSquare ℓ (Profinite.padicAlgClRingObj ℓ)
    g b c q p₂ p₂' f hgq hq₂ w₂ ((boundedConstructibleLowerStar _ ℓ f).obj K)
  have hε := (boundedConstructibleUpperStarComp _ ℓ c p₂').inv.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app K)
  simp only [Functor.comp_map] at hε
  dsimp only [Functor.id_obj] at hε
  rewrite [eqToHom_upperStar_tensor ℓ hgq]
  simp only [Category.assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight]
  rewrite [MonoidalCategory.rightUnitor_inv_comp_whiskerRight_comp_hom_assoc]
  simp only [prodUpperStarCounit, Functor.map_comp, Category.assoc]
  rewrite [hε, reassoc_of% hs]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj]

end Coefficient

end AlgebraicGeometry.ProEtale.CondensedRing
