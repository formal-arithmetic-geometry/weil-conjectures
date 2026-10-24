/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.LeftProjectionComp
public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalShift
public import WeilConjectures.TraceFormula.SourceExchangeTransport

/-!

# The class of the coefficient pushforward

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

lemma Adjunction.map_comp_mateEquiv_app_comp_counit {C₁ C₂ D₁ D₂ : Type*} [Category C₁]
    [Category C₂] [Category D₁] [Category D₂] {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂}
    {R₂ : D₂ ⥤ C₂} {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) {A : C₂} {B : C₁} {Xd : D₁} (γ : A ⟶ G.obj B) (u : B ⟶ R₁.obj Xd) :
    L₂.map (γ ≫ G.map u ≫ (mateEquiv adj₁ adj₂ α).app Xd) ≫ adj₂.counit.app (H.obj Xd) =
      L₂.map γ ≫ α.app B ≫ H.map (L₁.map u ≫ adj₁.counit.app Xd) := by
  have h₁ := mateEquiv_counit adj₁ adj₂ α Xd
  have h₂ := α.naturality u
  simp only [Functor.comp_map] at h₁ h₂
  simp only [Functor.map_comp, Category.assoc, h₁, reassoc_of% h₂]

@[reassoc]
lemma Functor.map_whiskerLeft_hom_app_comp_map_whiskerLeft_inv_app {B C D : Type*} [Category B]
    [Category C] [Category D] [MonoidalCategory C] (F : C ⥤ D) (A : C) {G H : B ⥤ C}
    (e : G ≅ H) (Z : B) : F.map (A ◁ e.hom.app Z) ≫ F.map (A ◁ e.inv.app Z) = 𝟙 _ := by
  rw [← F.map_comp, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_app,
    MonoidalCategory.whiskerLeft_id, F.map_id]

lemma Functor.map_map_comp_map_map_assoc_of_eq {B C D : Type*} [Category B] [Category C]
    [Category D] (F : C ⥤ D) (G : B ⥤ C) {X Y Y' Z : B} {x : X ⟶ Y} {y : Y ⟶ Z} {x' : X ⟶ Y'}
    {y' : Y' ⟶ Z} (h : x ≫ y = x' ≫ y') {W : D} (k : F.obj (G.obj Z) ⟶ W) :
    F.map (G.map x) ≫ F.map (G.map y) ≫ k = F.map (G.map x') ≫ F.map (G.map y') ≫ k := by
  rw [← F.map_comp_assoc, ← G.map_comp, h, G.map_comp, F.map_comp_assoc]

lemma Functor.map_comp₃_assoc_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Y' Z Z' W : C} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ W} {a' : X ⟶ Y'} {b' : Y' ⟶ Z'}
    {c' : Z' ⟶ W} (h : a ≫ b ≫ c = a' ≫ b' ≫ c') {V : D} (k : F.obj W ⟶ V) :
    F.map a ≫ F.map b ≫ F.map c ≫ k = F.map a' ≫ F.map b' ≫ F.map c' ≫ k := by
  simpa only [Functor.map_comp, Category.assoc] using congrArg (fun t ↦ F.map t ≫ k) h

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Generic

variable {C Y : Over (Spec (.of k))} [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

lemma lowerShriek_map_comp_eqToHom_comp_counit {s t : C ⟶ Y} (h : t = s)
    {N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (w : N ⟶ (boundedConstructibleUpperShriek _ ℓ t).obj M) :
    (boundedConstructibleLowerShriek _ ℓ s).map
        (w ≫ eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperShriek _ ℓ r).obj M) h)) ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ s).counit.app M =
    eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj N) h.symm) ≫
      (boundedConstructibleLowerShriek _ ℓ t).map w ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ t).counit.app M := by
  subst h
  simp

lemma lowerShriek_map_comp_comp_eqToHom_comp_counit {s t : C ⟶ Y} (h : t = s)
    {N N' : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (v : N' ⟶ N)
    (w : N ⟶ (boundedConstructibleUpperShriek _ ℓ t).obj M) :
    (boundedConstructibleLowerShriek _ ℓ s).map
        (v ≫ w ≫ eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperShriek _ ℓ r).obj M) h)) ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ s).counit.app M =
    (boundedConstructibleLowerShriek _ ℓ s).map v ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj N) h.symm) ≫
      (boundedConstructibleLowerShriek _ ℓ t).map w ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ t).counit.app M := by
  subst h
  simp

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The left projection morphisms of the compactly supported direct images compose. -/
lemma leftProjection_lowerShriek_comp (x : C ⟶ Y) (y : Y ⟶ Z)
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (T : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ (x ≫ y)) M T ≫
        (boundedConstructibleLowerShriek _ ℓ (x ≫ y)).map
          ((boundedConstructibleUpperStarComp _ ℓ x y).hom.app M ▷ T) =
      M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app T ≫
        Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ y) M
          ((boundedConstructibleLowerShriek _ ℓ x).obj T) ≫
        (boundedConstructibleLowerShriek _ ℓ y).map
          (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ x)
            ((boundedConstructibleUpperStar _ ℓ y).obj M) T) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app _ :=
  Verdier.leftProjection_comp _ _ _ _ _ (fun _ _ ↦ boundedConstructible_braiding_hom_braiding_hom _ _ _)
    (fun T M ↦ exceptionalProjection_comp ℓ x y T M) M T

set_option maxHeartbeats 2000000 in
-- the adjunctions of bounded constructible complexes are unfolded in the defeq checks
/-- The left projection morphism of a proper morphism at the unit point is the unit of the
adjunction. -/
lemma leftProjection_lowerShriek_unit (g : C ⟶ Y) [IsProper g.left]
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ◁ ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar _ ℓ g).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ g)).inv ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _)) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ g) M (𝟙_ _) =
    (ρ_ M).hom ≫ (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app M ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app _ ≫
      (boundedConstructibleLowerShriek _ ℓ g).map (ρ_ _).inv :=
  Verdier.leftProjection_unit _ _ _ _
    (fun T M ↦ upperStar_map_exceptionalProjection_comp_counit ℓ g T M)
    (fun A B ↦ boundedConstructibleUpperStar_map_braiding_hom_δ _ ℓ g A B)
    (fun _ _ ↦ boundedConstructible_braiding_hom_braiding_hom _ _ _) M

set_option maxHeartbeats 1000000 in
-- the compactly supported direct images are unfolded in the defeq checks
/-- The left projection morphism of a composite `g ≫ b` with `g` proper at the unit point. -/
lemma leftProjection_lowerShriek_comp_unit (g : C ⟶ Y) [IsProper g.left] (b : Y ⟶ Z)
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ◁ (boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app (𝟙_ _) ≫
          (boundedConstructibleLowerStar _ ℓ g).map
            (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ g)).inv ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _)) ≫
      M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app (𝟙_ _) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ (g ≫ b)) M (𝟙_ _) =
    Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ b) M (𝟙_ _) ≫
      (boundedConstructibleLowerShriek _ ℓ b).map
        ((ρ_ _).hom ≫ (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app _ ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app _ ≫
          (boundedConstructibleLowerShriek _ ℓ g).map (ρ_ _).inv) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app _ ≫
      (boundedConstructibleLowerShriek _ ℓ (g ≫ b)).map
        ((boundedConstructibleUpperStarComp _ ℓ g b).inv.app M ▷ _) := by
  have hc := leftProjection_lowerShriek_comp ℓ g b M (𝟙_ _)
  have hc' : Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ (g ≫ b)) M
      (𝟙_ _) =
      M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).hom.app (𝟙_ _) ≫
        Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ b) M
          ((boundedConstructibleLowerShriek _ ℓ g).obj (𝟙_ _)) ≫
        (boundedConstructibleLowerShriek _ ℓ b).map
          (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ g)
            ((boundedConstructibleUpperStar _ ℓ b).obj M) (𝟙_ _)) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app _ ≫
        (boundedConstructibleLowerShriek _ ℓ (g ≫ b)).map
          ((boundedConstructibleUpperStarComp _ ℓ g b).inv.app M ▷ _) := by
    simp only [← reassoc_of% hc, ← Functor.map_comp, ← comp_whiskerRight, Iso.hom_inv_id_app,
      id_whiskerRight]
    exact (Category.comp_id _).symm.trans (congrArg _ (CategoryTheory.Functor.map_id _ _).symm)
  have hn := Verdier.leftProjection_naturality (boundedConstructibleExceptionalProjection _ ℓ b) M
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar _ ℓ g).map
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ g)).inv ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _))
  have hu := leftProjection_lowerShriek_unit ℓ g ((boundedConstructibleUpperStar _ ℓ b).obj M)
  have hi : M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app (𝟙_ _) ≫
      M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).hom.app (𝟙_ _) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app, MonoidalCategory.whiskerLeft_id]
  rw [hc', ← Category.assoc (M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app (𝟙_ _)),
    hi, Category.id_comp, reassoc_of% hn, ← Functor.map_comp_assoc,
    hu]
  rfl

set_option maxHeartbeats 1000000 in
-- the compactly supported direct images are unfolded in the defeq checks
/-- `leftProjection_lowerShriek_comp_unit` for a composite `s = g ≫ b`, mapped by a functor. -/
lemma map_leftProjection_lowerShriek_comp_unit (g : C ⟶ Y) [IsProper g.left] (b : Y ⟶ Z)
    {s : C ⟶ Z} (h : g ≫ b = s) (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {D : Type*}
    [Category D] (F : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ D) {W : D}
    (k : F.obj ((boundedConstructibleLowerShriek _ ℓ s).obj
      ((boundedConstructibleUpperStar _ ℓ s).obj M ⊗ 𝟙_ _)) ⟶ W) :
    F.map (M ◁ (boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app (𝟙_ _))) ≫
      F.map (M ◁ (boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleLowerStar _ ℓ g).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ g)).inv)) ≫
      F.map (M ◁ (boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _))) ≫
      F.map (M ◁ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app (𝟙_ _)) ≫
      F.map (M ◁ eqToHom (by rw [h])) ≫
      F.map (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ s) M (𝟙_ _)) ≫
      k =
    F.map (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ b) M (𝟙_ _)) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ b).map (ρ_ _).hom) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ g).unit.app _)) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app _)) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleLowerShriek _ ℓ g).map (ρ_ _).inv)) ≫
      F.map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app _) ≫
      F.map ((boundedConstructibleLowerShriek _ ℓ (g ≫ b)).map
        ((boundedConstructibleUpperStarComp _ ℓ g b).inv.app M ▷ _)) ≫
      F.map (eqToHom (by rw [h])) ≫ k := by
  subst h
  have e := congrArg (fun t ↦ F.map t ≫ k) (leftProjection_lowerShriek_comp_unit ℓ g b M)
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc] at e
  simpa only [eqToHom_refl, MonoidalCategory.whiskerLeft_id, CategoryTheory.Functor.map_id,
    Category.id_comp] using e

@[reassoc]
lemma eqToHom_comp_lowerShriek_map {s t : C ⟶ Y} (h : s = t)
    {N N' : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : N ⟶ N') :
    eqToHom (by rw [h]) ≫ (boundedConstructibleLowerShriek _ ℓ t).map φ =
      (boundedConstructibleLowerShriek _ ℓ s).map φ ≫ eqToHom (by rw [h]) := by
  subst h
  simp

@[reassoc]
lemma whiskerLeft_eqToHom_comp_leftProjection {u v : C ⟶ Y} (h : u = v)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (T : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ◁ eqToHom (by rw [h] : (boundedConstructibleLowerShriek _ ℓ u).obj T =
        (boundedConstructibleLowerShriek _ ℓ v).obj T) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ v) M T =
    Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ u) M T ≫
      eqToHom (by rw [h]) := by
  subst h
  simp

end Generic

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.ProperPushforwardDiagram

variable {ℓ} {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y)

set_option maxHeartbeats 0 in
-- the compactly supported direct images are unfolded in the defeq checks
/-- The core of `class_pushforward`: the two ways of transporting `Rp₁'_! (Lp₂'^* K' ⊗ Rb_! 𝟙)`
to `Rf_* Rc₁_! Lc₂^* K` agree. -/
theorem class_pushforward_core :
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ P.pushforward.support)
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff) (𝟙_ _) ≫
          (boundedConstructibleLowerShriek _ ℓ P.pushforward.support).map
            ((ρ_ _).hom ≫ (boundedConstructibleUpperStarComp _ ℓ P.pushforward.support
              prod.snd).inv.app P.coeff)) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ P.pushforward.support prod.fst).inv.app
        ((boundedConstructibleUpperStar _ ℓ (P.pushforward.support ≫ prod.snd)).obj P.coeff) ≫
      (boundedConstructibleLowerShriek _ ℓ (P.pushforward.support ≫ prod.fst)).map
        (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj P.coeff)
          P.pushforward.support_snd)) ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj
        ((boundedConstructibleUpperStar _ ℓ P.b₂).obj P.coeff)) P.pushforward.support_fst) ≫
      (boundedConstructibleLowerShriek _ ℓ P.b₁).map P.pushforwardCoeffUnit ≫
      (lowerStarLowerShriekCompIso ℓ P.w₁).hom.app
        ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K) =
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff ◁
          (boundedConstructibleLowerShriek _ ℓ P.pushforward.support).map
            ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ P.g).unit.app (𝟙_ _) ≫
              (boundedConstructibleLowerStar _ ℓ P.g).map
                (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv)) ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff ◁
          (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom.app (𝟙_ _)) ≫
      (classTransport ℓ P.f K).app ((boundedConstructibleLowerShriek _ ℓ c.support).obj (𝟙_ _)) ≫
      (boundedConstructibleLowerStar _ ℓ P.f).map
        ((boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X)).map
            (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ c.support)
                ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K) (𝟙_ _) ≫
              (boundedConstructibleLowerShriek _ ℓ c.support).map
                ((ρ_ _).hom ≫ (boundedConstructibleUpperStarComp _ ℓ c.support prod.snd).inv.app K)) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.support prod.fst).inv.app
            ((boundedConstructibleUpperStar _ ℓ (c.support ≫ prod.snd)).obj K) ≫
          (boundedConstructibleLowerShriek _ ℓ (c.support ≫ prod.fst)).map
            (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj K)
              c.support_snd)) ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj
            ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K)) c.support_fst)) := by
  simp only [classTransport, lowerStarLowerShriekCompIso, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, eqToIso.hom, eqToHom_app, Category.id_comp,
    Category.comp_id, Functor.comp_map, Category.assoc]
  simp only [curriedTensor_obj_map, MonoidalCategory.whiskerLeft_comp, Functor.map_comp,
    Category.assoc] at *
  rw [Functor.map_whiskerLeft_hom_app_comp_map_whiskerLeft_inv_app_assoc]
  simp only [← Functor.map_comp (boundedConstructibleLowerStar _ ℓ P.f)]
  rw [← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ P.f).hom.naturality]
  simp only [← Category.assoc]
  refine congrArg (· ≫ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ P.f).hom.app _) ?_
  simp only [Category.assoc, Functor.map_comp, leftProjectionNatTrans, curriedTensor_map_app,
    curriedTensor_obj_obj]
  rw [Functor.map_map_comp_map_map_assoc_of_eq (boundedConstructibleLowerShriek _ ℓ P.f)
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X))
    (Verdier.leftProjection_naturality_left (boundedConstructibleExceptionalProjection _ ℓ c.support)
      (prodUpperStarCounit ℓ (prod.map_snd P.f P.f) K) (𝟙_ _))]
  have hsq := (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst P.f P.f)).hom.naturality
      (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ c.support)
        ((boundedConstructibleUpperStar _ ℓ (prod.map P.f P.f)).obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff)) (𝟙_ _))
  simp only [Functor.comp_map] at hsq
  rw [← reassoc_of% hsq]
  have hc := leftProjection_lowerShriek_comp ℓ c.support (prod.map P.f P.f)
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff) (𝟙_ _)
  have h₃ : (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff ◁
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.support (prod.map P.f P.f)).hom.app
          (𝟙_ _) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ (prod.map P.f P.f))
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff)
        ((boundedConstructibleLowerShriek _ ℓ c.support).obj (𝟙_ _)) ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.map P.f P.f)).map
        (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ c.support)
          ((boundedConstructibleUpperStar _ ℓ (prod.map P.f P.f)).obj
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff)) (𝟙_ _)) =
      Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ
          (c.support ≫ prod.map P.f P.f))
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff) (𝟙_ _) ≫
      (boundedConstructibleLowerShriek _ ℓ (c.support ≫ prod.map P.f P.f)).map
        ((boundedConstructibleUpperStarComp _ ℓ c.support (prod.map P.f P.f)).hom.app _ ▷ _) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.support (prod.map P.f P.f)).hom.app _ := by
    rw [reassoc_of% hc]
    simp
  conv_rhs => rw [Functor.map_comp₃_assoc_of_eq
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)) h₃]
  conv_rhs => rw [map_leftProjection_lowerShriek_comp_unit ℓ P.g P.pushforward.support P.g_comp_support]
  refine whisker_eq _ (whisker_eq _ ?_)
  done

set_option maxHeartbeats 2000000 in
-- the compactly supported direct images are unfolded in the defeq checks
/-- **The class of the coefficient pushforward** (blueprint `lem-trf-trace-source-exchange`,
identity (b)): `[δ ∘ Rg_* u ∘ γ] = Φ ∘ Rq_* [u] ∘ Ξ ∘ Rb_! η_g`. -/
theorem class_pushforward :
    P.pushforward.class =
      (boundedConstructibleLowerShriek _ ℓ P.pushforward.support).map
          ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ P.g).unit.app (𝟙_ _) ≫
            (boundedConstructibleLowerStar _ ℓ P.g).map
              (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv) ≫
        (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar _ ℓ (prod.map P.f P.f)).map c.class ≫
        classTransportMap ℓ P.f K := by
  apply classTest_injective
  rw [classTest_comp, classTest_comp, classTest_map_comp_classTransportMap]
  simp only [Correspondence.class]
  rw [classTest_correspondenceClassEquiv_symm, classTest_correspondenceClassEquiv_symm,
    lowerShriek_map_comp_comp_eqToHom_comp_counit ℓ P.pushforward.support_fst.symm,
    lowerShriek_map_comp_comp_eqToHom_comp_counit ℓ c.support_fst.symm]
  simp only [pushforwardCoeff, pushforwardCoeffCounit, lowerStarUpperShriekExchange]
  rw [Adjunction.map_comp_mateEquiv_app_comp_counit]
  have h := congrArg (· ≫ (boundedConstructibleLowerStar _ ℓ P.f).map
    ((boundedConstructibleLowerShriek _ ℓ c.c₁).map c.u ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ c.c₁).counit.app K)) P.class_pushforward_core
  simpa only [Functor.map_comp, Category.assoc] using h

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
