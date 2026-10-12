/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.PairCategory.Preadditive

/-!
# Descent of compatible families of functors to pair categories

Let `F` and `G` be pseudofunctors from a directed preorder to categories. A *compatible family*
`Φ : CompatibleFamily F G` consists of functors `Φ_i : F i ⥤ G i` and isomorphisms
`β_{j/i} : Φ_j ∘ T_{j/i} ≅ T_{j/i} ∘ Φ_i` satisfying the unit and associator equations
(it is a strong natural transformation `F ⟶ G`, written out componentwise). Such a family
descends to a functor `Φ.descent : PairCategory F ⥤ PairCategory G`, sending `(i, A)` to
`(i, Φ_i A)` and a representative `u : T_{k/i} A ⟶ T_{k/j} B` to
`β_{k/j} ∘ Φ_k(u) ∘ β_{k/i}⁻¹`. Compatible natural transformations descend to natural
transformations of the descended functors.

This is blueprint `prop-weil-pbc-descent-functors`.

## Main definitions

- `CategoryTheory.PairCategory.CompatibleFamily` : compatible families of functors.
- `CategoryTheory.PairCategory.CompatibleFamily.descent` : the descended functor.
- `CategoryTheory.PairCategory.CompatibleFamily.Hom` : compatible families of natural
  transformations, and `CompatibleFamily.Hom.descent` the descended natural transformation.

## Main results

- `CategoryTheory.PairCategory.CompatibleFamily.descent_map_homMk` : the value of the descended
  functor on a representative.
- `CategoryTheory.PairCategory.CompatibleFamily.inclCompDescentIso` : the descended functor
  extends `Φ_i` along the stage inclusions.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory Category Limits Pseudofunctor

namespace CategoryTheory.PairCategory

variable {ι : Type w} [Preorder ι] (F : Pseudofunctor (LocallyDiscrete ι) Cat.{v₁, u₁})
  (G : Pseudofunctor (LocallyDiscrete ι) Cat.{v₂, u₂})

/-- Blueprint `prop-weil-pbc-descent-functors`: a *compatible family* of functors between two
pseudofunctors from a preorder to categories: functors `Φ_i : F i ⥤ G i` with isomorphisms
`β_{j/i} : T_{j/i} ⋙ Φ_j ≅ Φ_i ⋙ T_{j/i}` satisfying the unit and associator equations. -/
structure CompatibleFamily where
  /-- The functor at stage `i`. -/
  functor (i : ι) : F.obj ⟨i⟩ ⥤ G.obj ⟨i⟩
  /-- The compatibility isomorphism `β_{j/i}`. -/
  iso ⦃i j : ι⦄ (h : i ≤ j) : F.transition h ⋙ functor j ≅ functor i ⋙ G.transition h
  /-- The associator equation. -/
  iso_comp ⦃i j k : ι⦄ (h₁ : i ≤ j) (h₂ : j ≤ k) (h : i ≤ k) (A : F.obj ⟨i⟩) :
    (iso h).hom.app A ≫ (G.transitionComp h₁ h₂ h).hom.app ((functor i).obj A) =
      (functor k).map ((F.transitionComp h₁ h₂ h).hom.app A) ≫
        (iso h₂).hom.app ((F.transition h₁).obj A) ≫
          (G.transition h₂).map ((iso h₁).hom.app A)
  /-- The unit equation. -/
  iso_id (i : ι) (h : i ≤ i) (A : F.obj ⟨i⟩) :
    (iso h).hom.app A ≫ (G.transitionId i h).hom.app ((functor i).obj A) =
      (functor i).map ((F.transitionId i h).hom.app A)

namespace CompatibleFamily

variable {F G} (Φ : CompatibleFamily F G)

/-- The inverse form of the associator equation. -/
@[reassoc]
lemma iso_comp_inv ⦃i j k : ι⦄ (h₁ : i ≤ j) (h₂ : j ≤ k) (h : i ≤ k) (A : F.obj ⟨i⟩) :
    (G.transitionComp h₁ h₂ h).inv.app ((Φ.functor i).obj A) ≫ (Φ.iso h).inv.app A =
      (G.transition h₂).map ((Φ.iso h₁).inv.app A) ≫
        (Φ.iso h₂).inv.app ((F.transition h₁).obj A) ≫
          (Φ.functor k).map ((F.transitionComp h₁ h₂ h).inv.app A) := by
  rw [← cancel_epi ((G.transition h₂).map ((Φ.iso h₁).hom.app A)),
    ← cancel_epi ((Φ.iso h₂).hom.app ((F.transition h₁).obj A)),
    ← cancel_epi ((Φ.functor k).map ((F.transitionComp h₁ h₂ h).hom.app A))]
  rw [← reassoc_of% Φ.iso_comp h₁ h₂ h A]
  simp [← Functor.map_comp, ← Functor.map_comp_assoc]

/-- The descent of a representative `u : T_{k/i} A ⟶ T_{k/j} B`:
`β_{k/j} ∘ Φ_k(u) ∘ β_{k/i}⁻¹ : T_{k/i} Φ_i A ⟶ T_{k/j} Φ_j B`. -/
def mapAt {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (u : X.at_ hX ⟶ Y.at_ hY) :
    (G.transition hX).obj ((Φ.functor X.idx).obj X.obj) ⟶
      (G.transition hY).obj ((Φ.functor Y.idx).obj Y.obj) :=
  (Φ.iso hX).inv.app X.obj ≫ (Φ.functor k).map u ≫ (Φ.iso hY).hom.app Y.obj

/-- The object `(i, Φ_i A)`. -/
abbrev obj (X : PairCategory F) : PairCategory G := ⟨X.idx, (Φ.functor X.idx).obj X.obj⟩

lemma mapAt_trHom {X Y : PairCategory F} {k k' : ι} (h : k ≤ k') (hX : X.idx ≤ k)
    (hY : Y.idx ≤ k) (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (u : X.at_ hX ⟶ Y.at_ hY) :
    Φ.mapAt hX' hY' (trHom h hX hY hX' hY' u) =
      trHom (X := Φ.obj X) (Y := Φ.obj Y) h hX hY hX' hY' (Φ.mapAt hX hY u) := by
  have eX := Φ.iso_comp hX h hX' X.obj
  have eY := Φ.iso_comp hY h hY' Y.obj
  have a : (Φ.iso hX').inv.app X.obj ≫
      (Φ.functor k').map ((F.transitionComp hX h hX').hom.app X.obj) =
      (G.transitionComp hX h hX').hom.app _ ≫ (G.transition h).map ((Φ.iso hX).inv.app X.obj) ≫
        (Φ.iso h).inv.app ((F.transition hX).obj X.obj) := by
    rw [← cancel_epi ((Φ.iso hX').hom.app X.obj), Iso.hom_inv_id_app_assoc, reassoc_of% eX]
    simp [← Functor.map_comp_assoc]
  have b : (Φ.functor k').map ((F.transitionComp hY h hY').inv.app Y.obj) ≫
      (Φ.iso hY').hom.app Y.obj =
      (Φ.iso h).hom.app ((F.transition hY).obj Y.obj) ≫
        (G.transition h).map ((Φ.iso hY).hom.app Y.obj) ≫
          (G.transitionComp hY h hY').inv.app _ := by
    rw [← cancel_epi ((Φ.functor k').map ((F.transitionComp hY h hY').hom.app Y.obj)),
      ← cancel_mono ((G.transitionComp hY h hY').hom.app _)]
    simp only [assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, id_comp,
      transitionComp_inv_hom_id_app, Functor.comp_obj, comp_id]
    exact eY
  have c := NatIso.naturality_1 (Φ.iso h) u
  simp only [Functor.comp_map] at c
  simp only [mapAt, trHom, Functor.map_comp, assoc]
  rw [reassoc_of% a, b, reassoc_of% c]

@[simp]
lemma mapAt_id {X : PairCategory F} {k : ι} (hX : X.idx ≤ k) :
    Φ.mapAt hX hX (𝟙 (X.at_ hX)) = 𝟙 _ := by
  simp [mapAt]

@[reassoc]
lemma mapAt_comp {X Y Z : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hZ : Z.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) (v : Y.at_ hY ⟶ Z.at_ hZ) :
    Φ.mapAt hX hZ (u ≫ v) = Φ.mapAt hX hY u ≫ Φ.mapAt hY hZ v := by
  simp [mapAt]

variable [IsDirected ι (· ≤ ·)]

lemma homMk_mapAt_eq {X Y : PairCategory F} {k k' : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (u : X.at_ hX ⟶ Y.at_ hY)
    (v : X.at_ hX' ⟶ Y.at_ hY') (e : homMk hX hY u = homMk hX' hY' v) :
    homMk (X := Φ.obj X) (Y := Φ.obj Y) hX hY (Φ.mapAt hX hY u) =
      homMk (X := Φ.obj X) (Y := Φ.obj Y) hX' hY' (Φ.mapAt hX' hY' v) := by
  obtain ⟨m, h, h', e⟩ := (homMk_eq_homMk_iff' _ _ _ _ _ _).1 e
  refine (homMk_eq_homMk_iff' _ _ _ _ _ _).2 ⟨m, h, h', ?_⟩
  rw [← mapAt_trHom, ← mapAt_trHom, e]

/-- Blueprint `prop-weil-pbc-descent-functors`: the functor `PairCategory F ⥤ PairCategory G`
induced by a compatible family of functors. -/
noncomputable def descent : PairCategory F ⥤ PairCategory G where
  obj := Φ.obj
  map {X Y} f := Quotient.liftOn f (fun r ↦ homMk (X := Φ.obj X) (Y := Φ.obj Y) r.le₁ r.le₂
    (Φ.mapAt r.le₁ r.le₂ r.hom))
    (fun r s h ↦ Φ.homMk_mapAt_eq _ _ _ _ _ _ (Quotient.sound h))
  map_id X := by
    change homMk (X := Φ.obj X) (Y := Φ.obj X) _ _ (Φ.mapAt _ _ (𝟙 _)) = _
    rw [mapAt_id, homMk_id]
  map_comp {X Y Z} f g := by
    obtain ⟨k, hX, hY, hZ, u, -, w, rfl, -, rfl⟩ := exists_homMk₃ f f g
    rw [homMk_comp_homMk]
    change homMk (X := Φ.obj X) (Y := Φ.obj Z) hX hZ (Φ.mapAt hX hZ (u ≫ w)) =
      homMk (X := Φ.obj X) (Y := Φ.obj Y) hX hY (Φ.mapAt hX hY u) ≫
        homMk (X := Φ.obj Y) (Y := Φ.obj Z) hY hZ (Φ.mapAt hY hZ w)
    rw [mapAt_comp, homMk_comp_homMk]

lemma descent_map_homMk {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (u : X.at_ hX ⟶ Y.at_ hY) :
    Φ.descent.map (homMk hX hY u) = homMk (X := Φ.obj X) (Y := Φ.obj Y) hX hY (Φ.mapAt hX hY u) :=
  rfl

lemma descent_obj (X : PairCategory F) : Φ.descent.obj X = ⟨X.idx, (Φ.functor X.idx).obj X.obj⟩ :=
  rfl

/-- The descended functor extends `Φ_i` along the stage inclusions. -/
lemma descent_map_incl_map (i : ι) {A B : F.obj ⟨i⟩} (u : A ⟶ B) :
    Φ.descent.map ((incl F i).map u) = (incl G i).map ((Φ.functor i).map u) := by
  change homMk (X := Φ.obj ⟨i, A⟩) (Y := Φ.obj ⟨i, B⟩) (le_refl i) le_rfl
      (Φ.mapAt (X := ⟨i, A⟩) (Y := ⟨i, B⟩) le_rfl le_rfl _) =
    homMk (X := (⟨i, (Φ.functor i).obj A⟩ : PairCategory G)) (Y := ⟨i, (Φ.functor i).obj B⟩)
      _ _ _
  congr 1
  have eA := Φ.iso_id i le_rfl A
  have eB := Φ.iso_id i le_rfl B
  simp only [mapAt, Functor.map_comp, assoc]
  rw [← cancel_epi ((Φ.iso (le_refl i)).hom.app A), Iso.hom_inv_id_app_assoc, ← eA]
  simp only [assoc]
  congr 2
  rw [← cancel_mono ((G.transitionId i le_rfl).hom.app ((Φ.functor i).obj B)), assoc, assoc,
    eB, ← Functor.map_comp]
  simp

/-- The descended functor extends `Φ_i` along the stage inclusions:
`j_i ⋙ Φ ≅ Φ_i ⋙ j_i`. -/
noncomputable def inclCompDescentIso (i : ι) :
    incl F i ⋙ Φ.descent ≅ Φ.functor i ⋙ incl G i :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun u ↦ by
    simp only [Functor.comp_map, descent_map_incl_map, Iso.refl_hom]
    exact (comp_id _).trans (id_comp _).symm)

/-- If every `Φ_i` is additive, so is the descended functor. -/
instance descent_additive [∀ i : ι, Preadditive (F.obj ⟨i⟩)]
    [∀ i : ι, Preadditive (G.obj ⟨i⟩)] [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).Additive]
    [∀ ⦃i j : ι⦄ (h : i ≤ j), (G.transition h).Additive] [∀ i, (Φ.functor i).Additive] :
    Φ.descent.Additive where
  map_add {X Y f g} := by
    obtain ⟨k, hX, hY, u, v, rfl, rfl⟩ := exists_homMk₂ f g
    rw [homMk_add_homMk, descent_map_homMk, descent_map_homMk, descent_map_homMk]
    refine Eq.trans ?_ (homMk_add_homMk (X := Φ.obj X) (Y := Φ.obj Y) _ _ _ _).symm
    congr 1
    simp [mapAt]

end CompatibleFamily

namespace CompatibleFamily

variable {F G} [IsDirected ι (· ≤ ·)]

/-- Blueprint `prop-weil-pbc-descent-functors`: a *compatible family of natural
transformations* `τ_i : Φ_i ⟶ Ψ_i`, i.e. one commuting with the isomorphisms `β`. -/
@[ext]
structure Hom (Φ Ψ : CompatibleFamily F G) where
  /-- The natural transformation at stage `i`. -/
  app (i : ι) : Φ.functor i ⟶ Ψ.functor i
  comm ⦃i j : ι⦄ (h : i ≤ j) (A : F.obj ⟨i⟩) :
    (Φ.iso h).hom.app A ≫ (G.transition h).map ((app i).app A) =
      (app j).app ((F.transition h).obj A) ≫ (Ψ.iso h).hom.app A := by cat_disch

attribute [reassoc] Hom.comm

variable {Φ Ψ Θ : CompatibleFamily F G}

/-- Blueprint `prop-weil-pbc-descent-functors`: the natural transformation of descended functors
induced by a compatible family of natural transformations; its component at `(i, A)` is
`j_i(τ_i A)`. -/
noncomputable def Hom.descent (τ : Hom Φ Ψ) : Φ.descent ⟶ Ψ.descent where
  app X := (incl G X.idx).map ((τ.app X.idx).app X.obj)
  naturality {X Y} f := by
    obtain ⟨k, hX, hY, u, rfl⟩ := exists_rep f
    rw [incl_map_eq_homMk hX, incl_map_eq_homMk hY]
    change homMk (X := Φ.obj X) (Y := Φ.obj Y) _ _ _ ≫ homMk (X := Φ.obj Y) (Y := Ψ.obj Y) _ _ _ =
      homMk (X := Φ.obj X) (Y := Ψ.obj X) _ _ _ ≫ homMk (X := Ψ.obj X) (Y := Ψ.obj Y) _ _ _
    rw [homMk_comp_homMk, homMk_comp_homMk]
    congr 1
    have a := τ.comm hX X.obj
    have b := τ.comm hY Y.obj
    simp only [mapAt, assoc]
    rw [b, ← cancel_epi ((Φ.iso hX).hom.app X.obj), Iso.hom_inv_id_app_assoc, reassoc_of% a,
      Iso.hom_inv_id_app_assoc, ← NatTrans.naturality_assoc]

lemma Hom.descent_app (τ : Hom Φ Ψ) (X : PairCategory F) :
    τ.descent.app X = (incl G X.idx).map ((τ.app X.idx).app X.obj) := rfl

/-- The identity compatible family of natural transformations. -/
@[simps]
def Hom.id (Φ : CompatibleFamily F G) : Hom Φ Φ where
  app i := 𝟙 _

/-- Composition of compatible families of natural transformations. -/
@[simps]
def Hom.comp (τ : Hom Φ Ψ) (σ : Hom Ψ Θ) : Hom Φ Θ where
  app i := τ.app i ≫ σ.app i
  comm := by
    intro i j h A
    simp only [NatTrans.comp_app, Functor.map_comp, τ.comm_assoc, σ.comm, assoc]

@[simp]
lemma Hom.descent_id (Φ : CompatibleFamily F G) : (Hom.id Φ).descent = 𝟙 Φ.descent := by
  ext X
  simp [Hom.descent_app]
  rfl

@[simp]
lemma Hom.descent_comp (τ : Hom Φ Ψ) (σ : Hom Ψ Θ) :
    (τ.comp σ).descent = τ.descent ≫ σ.descent := by
  ext X
  exact (incl G X.idx).map_comp _ _

end CompatibleFamily


namespace CompatibleFamily

variable {F G} {H : Pseudofunctor (LocallyDiscrete ι) Cat.{v₂, u₂}}

variable (F) in
/-- The identity compatible family. -/
@[simps]
def id : CompatibleFamily F F where
  functor _ := 𝟭 _
  iso _ _ _ := Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  iso_comp _ _ _ _ _ _ _ := by simp
  iso_id _ _ _ := by simp

/-- The composite of two compatible families. -/
@[simps functor]
def comp (Φ : CompatibleFamily F G) (Ψ : CompatibleFamily G H) : CompatibleFamily F H where
  functor i := Φ.functor i ⋙ Ψ.functor i
  iso _ _ h := (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Φ.iso h) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Ψ.iso h) ≪≫
    (Functor.associator _ _ _).symm
  iso_comp i j k h₁ h₂ h A := by
    have e₁ := Φ.iso_comp h₁ h₂ h A
    have e₂ := Ψ.iso_comp h₁ h₂ h ((Φ.functor i).obj A)
    simp only [Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app, id_comp,
      comp_id, assoc, Functor.comp_map, Functor.map_comp] at e₂ ⊢
    rw [e₂, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, e₁]
    simp only [Functor.map_comp, assoc]
    congr 2
    exact (Ψ.iso h₂).hom.naturality_assoc ((Φ.iso h₁).hom.app A) _
  iso_id i h A := by
    have e₁ := Φ.iso_id i h A
    have e₂ := Ψ.iso_id i h ((Φ.functor i).obj A)
    simp only [Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app, id_comp,
      comp_id, assoc, Functor.comp_map] at e₂ ⊢
    rw [e₂, ← Functor.map_comp, e₁]

lemma comp_iso_hom_app (Φ : CompatibleFamily F G) (Ψ : CompatibleFamily G H) ⦃i j : ι⦄
    (h : i ≤ j) (A : F.obj ⟨i⟩) :
    ((Φ.comp Ψ).iso h).hom.app A =
      (Ψ.functor j).map ((Φ.iso h).hom.app A) ≫ (Ψ.iso h).hom.app ((Φ.functor i).obj A) := by
  simp [comp]

lemma comp_iso_inv_app (Φ : CompatibleFamily F G) (Ψ : CompatibleFamily G H) ⦃i j : ι⦄
    (h : i ≤ j) (A : F.obj ⟨i⟩) :
    ((Φ.comp Ψ).iso h).inv.app A =
      (Ψ.iso h).inv.app ((Φ.functor i).obj A) ≫ (Ψ.functor j).map ((Φ.iso h).inv.app A) := by
  simp [comp]

variable [IsDirected ι (· ≤ ·)]

/-- The descent of the identity family is the identity functor. -/
noncomputable def descentIdIso : (CompatibleFamily.id F).descent ≅ 𝟭 (PairCategory F) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {X Y} f ↦ by
    obtain ⟨k, hX, hY, u, rfl⟩ := exists_rep f
    rw [descent_map_homMk]
    simp only [Iso.refl_hom, Functor.id_map]
    refine (comp_id _).trans (Eq.trans ?_ (id_comp _).symm)
    congr 1
    simp only [mapAt, id_iso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app]
    erw [id_comp, id_comp, comp_id, comp_id]
    rfl)

/-- The descent of a composite family is the composite of the descents. -/
noncomputable def descentCompIso (Φ : CompatibleFamily F G) (Ψ : CompatibleFamily G H) :
    (Φ.comp Ψ).descent ≅ Φ.descent ⋙ Ψ.descent :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {X Y} f ↦ by
    obtain ⟨k, hX, hY, u, rfl⟩ := exists_rep f
    simp only [Iso.refl_hom, Functor.comp_map, descent_map_homMk]
    refine (comp_id _).trans (Eq.trans ?_ (id_comp _).symm)
    change homMk (X := (Φ.comp Ψ).obj X) (Y := (Φ.comp Ψ).obj Y) _ _ _ =
      homMk (X := Ψ.obj (Φ.obj X)) (Y := Ψ.obj (Φ.obj Y)) _ _ _
    congr 1
    simp [mapAt, comp_iso_hom_app, comp_iso_inv_app]
    rfl)

lemma descent_id_map {X Y : PairCategory F} (f : X ⟶ Y) :
    (CompatibleFamily.id F).descent.map f = f := by
  simpa using descentIdIso.hom.naturality f

lemma descent_comp_map (Φ : CompatibleFamily F G) (Ψ : CompatibleFamily G H)
    {X Y : PairCategory F} (f : X ⟶ Y) :
    (Φ.comp Ψ).descent.map f = Ψ.descent.map (Φ.descent.map f) := by
  simpa using (descentCompIso Φ Ψ).hom.naturality f

instance Hom.isIso_descent {Φ Ψ : CompatibleFamily F G} (τ : Hom Φ Ψ) [∀ i, IsIso (τ.app i)] :
    IsIso τ.descent := by
  have (X : PairCategory F) : IsIso (τ.descent.app X) := by
    rw [Hom.descent_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end CompatibleFamily

end CategoryTheory.PairCategory
