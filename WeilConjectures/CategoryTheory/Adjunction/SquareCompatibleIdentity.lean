/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate

/-!
# Compatibility of identifications with the identity functor

Let `T : A ⥤ A'` be a functor relating two "levels" of categories, and let `U : A ⥤ A` and
`U' : A' ⥤ A'` be endofunctors identified with the identity functors by `u : U ≅ 𝟭` and
`u' : U' ≅ 𝟭`, with a commutation square `ι : U ⋙ T ≅ T ⋙ U'`. This file gives two criteria
for `u` and `u'` to be compatible with `ι` (`CategoryTheory.NatTrans.SquareCompatible`):

* `NatTrans.SquareCompatible.of_comp_unit`: if `ι` is compatible with "comultiplications"
  `d : U ⟶ U ⋙ U` and `d' : U' ⟶ U' ⋙ U'` that are sections of `u` and `u'` (as is the
  composition isomorphism `(𝟙 ≫ 𝟙)^* ≅ 𝟙^* ⋙ 𝟙^*` of a pseudofunctor, by its unit law);
* `NatTrans.SquareCompatible.of_adjunction`: for left adjoints `L` and `L'` identified with the
  identity, with right adjoints identified with the identity compatibly with the mated
  commutation square, by identifications related to the counits.

It also records the equation of a compatibility with a pasted commutation square solved for the
components of the squares (`NatTrans.SquareCompatible.inv_app_comp_pasteSquareIso`).
-/

@[expose] public section

namespace CategoryTheory

/-- Two natural transformations `F ⟶ G` out of a category `A` agree if they agree at the objects
`U K`, for an endofunctor `U` of `A` isomorphic to the identity. -/
lemma NatTrans.ext_of_iso_id {A B : Type*} [Category* A] [Category* B] {F G : A ⥤ B}
    {α β : F ⟶ G} {U : A ⥤ A} (u : U ≅ 𝟭 A) (h : ∀ K, α.app (U.obj K) = β.app (U.obj K)) :
    α = β := by
  ext K
  have h₁ := α.naturality (u.hom.app K)
  have h₂ := β.naturality (u.hom.app K)
  dsimp only [Functor.id_obj] at h₁ h₂
  rw [← cancel_epi (F.map (u.hom.app K)), h₁, h₂, h]

namespace NatTrans.SquareCompatible

variable {A A' : Type*} [Category* A] [Category* A'] {T : A ⥤ A'}

/-- Pointwise version of `NatTrans.ext_of_iso_id` for the equation of a compatibility with the
identity square. -/
private lemma app_eq_of_iso_id {U : A ⥤ A} {U' : A' ⥤ A'} (ι : U ⋙ T ≅ T ⋙ U') (v : U ≅ 𝟭 A)
    (v' : U' ≅ 𝟭 A') {W : A ⥤ A} (w : W ≅ 𝟭 A)
    (h : ∀ K, T.map (v.hom.app (W.obj K)) = ι.hom.app (W.obj K) ≫ v'.hom.app (T.obj (W.obj K)))
    (K : A) : T.map (v.hom.app K) = ι.hom.app K ≫ v'.hom.app (T.obj K) := by
  have := NatTrans.ext_of_iso_id (α := Functor.whiskerRight v.hom T)
    (β := ι.hom ≫ Functor.whiskerLeft T v'.hom) w (fun K ↦ by simpa using h K)
  simpa using congrArg (fun γ ↦ γ.app K) this

/-- Identifications `u : U ≅ 𝟭` and `u' : U' ≅ 𝟭` are compatible with a commutation square
`ι : U ⋙ T ≅ T ⋙ U'` if `ι` is compatible with transformations `d : U ⟶ U ⋙ U` and
`d' : U' ⟶ U' ⋙ U'` which are sections of `u` and `u'` at the objects `U K`. -/
lemma of_comp_unit {U : A ⥤ A} {U' : A' ⥤ A'} {ι : U ⋙ T ≅ T ⋙ U'} (u : U ≅ 𝟭 A)
    (u' : U' ≅ 𝟭 A') {d : U ⟶ U ⋙ U} {d' : U' ⟶ U' ⋙ U'}
    (hd : ∀ K, d.app K ≫ u.hom.app (U.obj K) = 𝟙 _)
    (hd' : ∀ K, d'.app K ≫ u'.hom.app (U'.obj K) = 𝟙 _)
    (h : SquareCompatible ι (Functor.pasteSquareIso ι ι) d d') :
    SquareCompatible ι (Functor.idSquareIso T) u.hom u'.hom := by
  have e (K : A) : d.app K = u.inv.app (U.obj K) := by
    rw [← cancel_mono (u.hom.app (U.obj K)), hd]
    simp
  have e' (K : A') : d'.app K = u'.inv.app (U'.obj K) := by
    rw [← cancel_mono (u'.hom.app (U'.obj K)), hd']
    simp
  intro K
  simp only [Functor.idSquareIso_hom_app, Functor.comp_obj, Functor.id_obj, Category.comp_id]
  refine app_eq_of_iso_id ι u u' u (fun K ↦ ?_) K
  have h₁ := h K
  rw [Functor.pasteSquareIso_hom_app, e, e'] at h₁
  have h₂ : ι.hom.app (U.obj K) = T.map (u.hom.app (U.obj K)) ≫ ι.hom.app K ≫
      u'.inv.app (U'.obj (T.obj K)) ≫ U'.map (ι.inv.app K) := by
    rw [← reassoc_of% h₁]
    simp [← Functor.map_comp, ← Functor.map_comp_assoc]
  rw [h₂]
  have h₃ := u'.hom.naturality (ι.inv.app K)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map] at h₃
  simp [h₃]

/-- Let `L ⊣ R` and `L' ⊣ R'` be adjunctions of endofunctors with mated commutation squares
`ιL` and `ιR`, and let `φ : L ≅ 𝟭`, `u : R ≅ 𝟭` (and their primed versions) be identifications
with `φ⁻¹ ≫ ε = u` on `R`. If `u` and `u'` are compatible with `ιR`, then `φ` and `φ'` are
compatible with `ιL`. -/
lemma of_adjunction {L R : A ⥤ A} {L' R' : A' ⥤ A'} {adj : L ⊣ R} {adj' : L' ⊣ R'}
    {ιL : L ⋙ T ≅ T ⋙ L'} {ιR : R ⋙ T ≅ T ⋙ R'} (hm : adj.IsMateSquare adj' ιL ιR)
    (φ : L ≅ 𝟭 A) (φ' : L' ≅ 𝟭 A') (u : R ≅ 𝟭 A) (u' : R' ≅ 𝟭 A')
    (hφ : ∀ W, φ.inv.app (R.obj W) ≫ adj.counit.app W = u.hom.app W)
    (hφ' : ∀ W, φ'.inv.app (R'.obj W) ≫ adj'.counit.app W = u'.hom.app W)
    (hu : SquareCompatible ιR (Functor.idSquareIso T) u.hom u'.hom) :
    SquareCompatible ιL (Functor.idSquareIso T) φ.hom φ'.hom := by
  have c (W : A) : adj.counit.app W = φ.hom.app (R.obj W) ≫ u.hom.app W := by
    rw [← hφ, Iso.hom_inv_id_app_assoc]
  have c' (W : A') : adj'.counit.app W = φ'.hom.app (R'.obj W) ≫ u'.hom.app W := by
    rw [← hφ', Iso.hom_inv_id_app_assoc]
  intro K
  simp only [Functor.idSquareIso_hom_app, Functor.comp_obj, Functor.id_obj, Category.comp_id]
  refine app_eq_of_iso_id ιL φ φ' u (fun W ↦ ?_) K
  have hc := counit hm W
  have hu' := hu W
  simp only [Functor.idSquareIso_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.comp_id] at hc hu'
  rw [Functor.pasteSquareIso_hom_app, c, c', Functor.map_comp, hu'] at hc
  have hn := φ'.hom.naturality (ιR.hom.app W)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map] at hn
  rw [← cancel_mono (ιR.hom.app W ≫ u'.hom.app (T.obj W))]
  simp only [Functor.id_obj, Functor.comp_obj, Category.assoc] at hc ⊢
  rw [hc, reassoc_of% hn]

end NatTrans.SquareCompatible

namespace NatTrans.SquareCompatible

variable {A B A' B' D D' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Category* D] [Category* D'] {T : A ⥤ A'} {T' : B ⥤ B'} {S : D ⥤ D'}

/-- The equation of a compatibility with a pasted commutation square, solved for the components
of the commutation squares. -/
lemma inv_app_comp_pasteSquareIso {F : A ⥤ B} {F' : A' ⥤ B'} {ιF : F ⋙ T' ≅ T ⋙ F'}
    {F₁ : A ⥤ D} {F₂ : D ⥤ B} {F₁' : A' ⥤ D'} {F₂' : D' ⥤ B'} {ι₁ : F₁ ⋙ S ≅ T ⋙ F₁'}
    {ι₂ : F₂ ⋙ T' ≅ S ⋙ F₂'} {α : F ⟶ F₁ ⋙ F₂} {α' : F' ⟶ F₁' ⋙ F₂'}
    (h : SquareCompatible ιF (Functor.pasteSquareIso ι₁ ι₂) α α') (K : A) :
    ιF.inv.app K ≫ T'.map (α.app K) ≫ ι₂.hom.app (F₁.obj K) =
      α'.app (T.obj K) ≫ F₂'.map (ι₁.inv.app K) := by
  have hK := h K
  rw [Functor.pasteSquareIso_hom_app] at hK
  rw [← cancel_mono (F₂'.map (ι₁.hom.app K))]
  simp only [Category.assoc, hK, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp

end NatTrans.SquareCompatible

end CategoryTheory
