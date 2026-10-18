/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# The Künneth map and its transport along a right adjoint with a projection formula

In a braided monoidal closed category, a pairing `ev : D ⊗ A ⟶ W` and an object `S` give the
*Künneth map* `S ⊗ D ⟶ [A, S ⊗ W]` (`CategoryTheory.pairingKunnethMap`), the transpose of
`A ⊗ (S ⊗ D) ≅ S ⊗ (D ⊗ A) ⟶ S ⊗ W`. For the evaluation pairing `[N, ω] ⊗ N ⟶ ω` of an object `N`
pulled back to a product, it is the map `S ⊗ q^*[N, ω] ⟶ [q^* N, S ⊗ q^* ω]` behind the
Künneth–Verdier isomorphism.

Let `L ⊣ R` be an adjunction with an invertible projection map `π : L M ⊗ N ≅ L(M ⊗ F N)`, for a
functor `F` with a comparison `δ : F(N ⊗ N') ≅ F N ⊗ F N'`, and let
`τ : R M ⊗ F N ⟶ R(M ⊗ N)` be the tensor map (`CategoryTheory.Adjunction.projectionTensorMap`).
The *internal Hom exchange* `R [A, Y] ⟶ [F A, R Y]` (`CategoryTheory.Adjunction.ihomExchange`)
is an isomorphism, and `R` carries the Künneth map of `ev` at `S` to the Künneth map of
`F ev` at `R S`, through `τ` (`CategoryTheory.Adjunction.projectionTensorMap_comp_map_pairingKunnethMap`).
So, if `τ` is invertible at `(S, D)` and `(S, W)`, then `R` of the Künneth map is invertible if and
only if the Künneth map of `F ev` at `R S` is
(`CategoryTheory.Adjunction.isIso_map_pairingKunnethMap_iff`).

## Main definitions

- `CategoryTheory.pairingKunnethMap`
- `CategoryTheory.Adjunction.ihomExchange`

## Main statements

- `CategoryTheory.Adjunction.isIso_ihomExchange`
- `CategoryTheory.Adjunction.isIso_map_pairingKunnethMap_iff`
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory MonoidalClosed

section KunnethMap

variable {E : Type*} [Category* E] [MonoidalCategory E] [BraidedCategory E] [MonoidalClosed E]

/-- The **Künneth map** of a pairing `ev : D ⊗ A ⟶ W` at an object `S`:
`S ⊗ D ⟶ [A, S ⊗ W]`, the transpose of `A ⊗ (S ⊗ D) ≅ S ⊗ (D ⊗ A) ⟶ S ⊗ W`. -/
noncomputable def pairingKunnethMap {A D W : E} (ev : D ⊗ A ⟶ W) (S : E) :
    S ⊗ D ⟶ (ihom A).obj (S ⊗ W) :=
  curry ((β_ (S ⊗ D) A).inv ≫ (α_ S D A).hom ≫ S ◁ ev)

lemma uncurry_pairingKunnethMap {A D W : E} (ev : D ⊗ A ⟶ W) (S : E) :
    uncurry (pairingKunnethMap ev S) = (β_ (S ⊗ D) A).inv ≫ (α_ S D A).hom ≫ S ◁ ev :=
  uncurry_curry _

/-- The Künneth map is natural in `S`. -/
@[reassoc]
lemma pairingKunnethMap_naturality {A D W : E} (ev : D ⊗ A ⟶ W) {S S' : E} (f : S ⟶ S') :
    f ▷ D ≫ pairingKunnethMap ev S' = pairingKunnethMap ev S ≫ (ihom A).map (f ▷ W) := by
  rw [pairingKunnethMap, ← curry_natural_left, pairingKunnethMap, ← curry_natural_right]
  congr 1
  rw [BraidedCategory.braiding_inv_naturality_right_assoc, associator_naturality_left_assoc,
    ← whisker_exchange, Category.assoc, Category.assoc]

/-- Whether the Künneth map is an isomorphism only depends on `S` up to isomorphism. -/
lemma isIso_pairingKunnethMap_iff_of_iso {A D W : E} (ev : D ⊗ A ⟶ W) {S S' : E} (e : S ≅ S') :
    IsIso (pairingKunnethMap ev S) ↔ IsIso (pairingKunnethMap ev S') := by
  have h : pairingKunnethMap ev S' =
      e.inv ▷ D ≫ pairingKunnethMap ev S ≫ (ihom A).map (e.hom ▷ W) := by
    rw [← pairingKunnethMap_naturality, ← comp_whiskerRight_assoc, e.inv_hom_id, id_whiskerRight,
      Category.id_comp]
  rw [h, isIso_comp_left_iff, isIso_comp_right_iff]

/-- The Künneth map only depends on the pairing up to isomorphism. -/
lemma pairingKunnethMap_comp_of_iso {A A' D D' W W' : E} (ev : D ⊗ A ⟶ W) (ev' : D' ⊗ A' ⟶ W')
    (a : A ≅ A') (d : D ≅ D') (w : W ≅ W') (h : d.hom ▷ A ≫ D' ◁ a.hom ≫ ev' = ev ≫ w.hom)
    (S : E) :
    S ◁ d.hom ≫ pairingKunnethMap ev' S =
      pairingKunnethMap ev S ≫ (ihom A).map (S ◁ w.hom) ≫ (pre a.inv).app (S ⊗ W') := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pairingKunnethMap]
  conv_rhs => rw [← Category.assoc, uncurry_pre_app,
    uncurry_natural_right,
    uncurry_pairingKunnethMap]
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_inv_naturality_right_assoc,
    BraidedCategory.braiding_inv_naturality_left_assoc, associator_naturality_middle_assoc,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
  congr 3
  rw [← h, whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- Whether the Künneth map is an isomorphism only depends on the pairing up to isomorphism. -/
lemma isIso_pairingKunnethMap_iff_of_iso_pairing {A A' D D' W W' : E} (ev : D ⊗ A ⟶ W)
    (ev' : D' ⊗ A' ⟶ W') (a : A ≅ A') (d : D ≅ D') (w : W ≅ W')
    (h : d.hom ▷ A ≫ D' ◁ a.hom ≫ ev' = ev ≫ w.hom) (S : E) :
    IsIso (pairingKunnethMap ev S) ↔ IsIso (pairingKunnethMap ev' S) := by
  have e := pairingKunnethMap_comp_of_iso ev ev' a d w h S
  have : IsIso ((pre a.inv).app (S ⊗ W')) :=
    ⟨(pre a.hom).app _, by simp [← NatTrans.comp_app, ← pre_map], by
      simp [← NatTrans.comp_app, ← pre_map]⟩
  rw [← isIso_comp_right_iff _ ((ihom A).map (S ◁ w.hom) ≫ (pre a.inv).app (S ⊗ W')), ← e,
    isIso_comp_left_iff]

/-- The Künneth map of the evaluation pairing `[N, ω] ⊗ N ⟶ ω` at the unit is an isomorphism. -/
lemma isIso_pairingKunnethMap_unit (N ω : E) :
    IsIso (pairingKunnethMap ((β_ ((ihom N).obj ω) N).hom ≫ (ihom.ev N).app ω) (𝟙_ E)) := by
  have : pairingKunnethMap ((β_ ((ihom N).obj ω) N).hom ≫ (ihom.ev N).app ω) (𝟙_ E) =
      (λ_ _).hom ≫ (ihom N).map (λ_ ω).inv := by
    rw [eq_comm, ← curry_uncurry ((λ_ _).hom ≫ _), pairingKunnethMap]
    congr 1
    rw [uncurry_natural_right, ← Category.comp_id (λ_ _).hom, uncurry_natural_left,
      uncurry_id_eq_ev]
    have key : (β_ (𝟙_ E ⊗ (ihom N).obj ω) N).inv ≫ (α_ (𝟙_ E) ((ihom N).obj ω) N).hom ≫
        (λ_ ((ihom N).obj ω ⊗ N)).hom = N ◁ (λ_ ((ihom N).obj ω)).hom ≫
          (β_ ((ihom N).obj ω) N).inv := by
      rw [leftUnitor_tensor_hom, Iso.hom_inv_id_assoc,
        BraidedCategory.braiding_inv_naturality_right]
    rw [id_whiskerLeft, reassoc_of% key]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  rw [this]
  infer_instance

end KunnethMap

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
  {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]

/-- The **internal Hom exchange** `R [A, Y] ⟶ [F A, R Y]` of an adjunction `L ⊣ R` with a
projection map: the transpose of
`F A ⊗ R [A, Y] ≅ R [A, Y] ⊗ F A ⟶ R ([A, Y] ⊗ A) ≅ R (A ⊗ [A, Y]) ⟶ R Y`, built from the tensor
map `τ` and the evaluation. -/
noncomputable def ihomExchange (A Y : D) :
    R.obj ((ihom A).obj Y) ⟶ (ihom (F.obj A)).obj (R.obj Y) :=
  curry ((β_ (R.obj ((ihom A).obj Y)) (F.obj A)).inv ≫ adj.projectionTensorMap π _ A ≫
    R.map ((β_ ((ihom A).obj Y) A).hom ≫ (ihom.ev A).app Y))

variable (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D),
  L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
include hπ

/-- Composing with the internal Hom exchange is, up to the curry bijections and the adjunction,
precomposition with the isomorphism `L(F A ⊗ T) ≅ L(T ⊗ F A) ≅ L T ⊗ A ≅ A ⊗ L T`. -/
lemma homEquiv_symm_uncurry_comp_ihomExchange {T : C} {A Y : D}
    (g : T ⟶ R.obj ((ihom A).obj Y)) :
    (adj.homEquiv _ _).symm (uncurry (g ≫ adj.ihomExchange π A Y)) =
      L.map (β_ T (F.obj A)).inv ≫ inv (π T A) ≫ (β_ (L.obj T) A).hom ≫
        uncurry ((adj.homEquiv _ _).symm g) := by
  have h := hπ g A
  rw [← cancel_epi (inv (π T A)), ← cancel_mono (inv (π _ A))] at h
  simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
  rw [ihomExchange, uncurry_natural_left, uncurry_curry, homEquiv_counit, homEquiv_counit,
    uncurry_eq]
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality,
    Adjunction.counit_naturality_assoc, map_projectionTensorMap_comp_counit_assoc]
  rw [← Functor.map_comp_assoc, BraidedCategory.braiding_inv_naturality_right, Functor.map_comp,
    Category.assoc, ← reassoc_of% h, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left_assoc, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]

/-- The internal Hom exchange is an isomorphism. -/
theorem isIso_ihomExchange (A Y : D) : IsIso (adj.ihomExchange π A Y) := by
  refine isIso_of_yoneda_map_bijective _ fun T ↦ ?_
  let ι : L.obj (F.obj A ⊗ T) ≅ A ⊗ L.obj T :=
    L.mapIso (β_ T (F.obj A)).symm ≪≫ (asIso (π T A)).symm ≪≫ β_ (L.obj T) A
  let e : (T ⟶ R.obj ((ihom A).obj Y)) ≃ (T ⟶ (ihom (F.obj A)).obj (R.obj Y)) :=
    (adj.homEquiv _ _).symm.trans (((ihom.adjunction A).homEquiv _ _).symm.trans
      ((ι.homCongr (Iso.refl Y)).symm.trans ((adj.homEquiv _ _).trans
        ((ihom.adjunction (F.obj A)).homEquiv _ _))))
  convert e.bijective using 1
  funext g
  rw [← curry_uncurry (g ≫ adj.ihomExchange π A Y),
    ← (adj.homEquiv _ _).apply_symm_apply (uncurry (g ≫ adj.ihomExchange π A Y)),
    homEquiv_symm_uncurry_comp_ihomExchange adj π hπ g]
  simp only [e, Equiv.trans_apply, homEquiv_apply_eq, homEquiv_symm_apply_eq]
  congr 2
  simp [ι, Iso.homCongr]

variable (hπr : ∀ (M : C) {N N' : D} (φ : N ⟶ N'),
    L.obj M ◁ φ ≫ π M N' = π M N ≫ L.map (M ◁ F.map φ))
  (δ : ∀ N N' : D, F.obj (N ⊗ N') ⟶ F.obj N ⊗ F.obj N') [∀ N N', IsIso (δ N N')]
  (hassoc : ∀ (M : C) (N N' : D), π M N ▷ N' ≫ π (M ⊗ F.obj N) N' ≫
    L.map (α_ M (F.obj N) (F.obj N')).hom = (α_ _ N N').hom ≫ π M (N ⊗ N') ≫ L.map (M ◁ δ N N'))
include hπr hassoc

/-- **Transport of the Künneth map.** Through the tensor maps `τ` and the internal Hom exchange,
`R` of the Künneth map of `ev : D ⊗ A ⟶ W` at `S` is the Künneth map of
`F D ⊗ F A ≅ F(D ⊗ A) ⟶ F W` at `R S`. -/
theorem projectionTensorMap_comp_map_pairingKunnethMap {A Dd W : D} (ev : Dd ⊗ A ⟶ W) (S : D) :
    adj.projectionTensorMap π S Dd ≫ R.map (pairingKunnethMap ev S) ≫ adj.ihomExchange π A (S ⊗ W) =
      pairingKunnethMap (inv (δ Dd A) ≫ F.map ev) (R.obj S) ≫
        (ihom (F.obj A)).map (adj.projectionTensorMap π S W) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, ihomExchange, uncurry_curry,
    uncurry_natural_right, uncurry_pairingKunnethMap]
  rw [BraidedCategory.braiding_inv_naturality_right_assoc,
    BraidedCategory.braiding_inv_naturality_right_assoc,
    projectionTensorMap_naturality_left_assoc adj π hπ, ← R.map_comp,
    BraidedCategory.braiding_naturality_left_assoc, ← uncurry_eq, uncurry_pairingKunnethMap,
    Iso.hom_inv_id_assoc, R.map_comp]
  have ha := adj.projectionTensorMap_assoc π hπ δ hassoc S Dd A
  have hr := projectionTensorMap_naturality_right adj π hπr S ev
  simp only [Category.assoc] at ha ⊢
  rw [reassoc_of% ha, ← hr, MonoidalCategory.whiskerLeft_comp_assoc]

/-- **Transport of the Künneth map.** If the tensor maps `τ` of `L ⊣ R` at `(S, D)` and
`(S, W)` are isomorphisms, then `R` of the Künneth map of `ev : D ⊗ A ⟶ W` at `S` is an
isomorphism if and only if the Künneth map of `F D ⊗ F A ≅ F(D ⊗ A) ⟶ F W` at `R S` is. -/
theorem isIso_map_pairingKunnethMap_iff {A Dd W : D} (ev : Dd ⊗ A ⟶ W) (S : D)
    [IsIso (adj.projectionTensorMap π S Dd)] [IsIso (adj.projectionTensorMap π S W)] :
    IsIso (R.map (pairingKunnethMap ev S)) ↔ IsIso (pairingKunnethMap (inv (δ Dd A) ≫ F.map ev) (R.obj S)) := by
  have := adj.isIso_ihomExchange π hπ A (S ⊗ W)
  have h := adj.projectionTensorMap_comp_map_pairingKunnethMap π hπ hπr δ hassoc ev S
  constructor
  · intro
    have : IsIso (pairingKunnethMap (inv (δ Dd A) ≫ F.map ev) (R.obj S) ≫
        (ihom (F.obj A)).map (adj.projectionTensorMap π S W)) := by
      rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((ihom (F.obj A)).map (adj.projectionTensorMap π S W))
  · intro
    have : IsIso (adj.projectionTensorMap π S Dd ≫ R.map (pairingKunnethMap ev S) ≫
        adj.ihomExchange π A (S ⊗ W)) := by
      rw [h]; infer_instance
    have : IsIso (R.map (pairingKunnethMap ev S) ≫ adj.ihomExchange π A (S ⊗ W)) :=
      IsIso.of_isIso_comp_left (adj.projectionTensorMap π S Dd) _
    exact IsIso.of_isIso_comp_right _ (adj.ihomExchange π A (S ⊗ W))

end Adjunction

section Dualizable

open Adjunction

variable {E : Type*} [Category* E] [MonoidalCategory E] [BraidedCategory E] [MonoidalClosed E]

/-- The counit of `Tᘁ ⊗ - ⊣ T ⊗ -`. -/
lemma tensorLeftAdjunction_counit_app' (T : E) [HasRightDual T] (X : E) :
    (tensorLeftAdjunction T Tᘁ).counit.app X =
      (α_ Tᘁ T X).inv ≫ ε_ T Tᘁ ▷ X ≫ (λ_ X).hom := by
  simp [tensorLeftAdjunction, tensorLeftHomEquiv]

/-- The tensor map of `Tᘁ ⊗ - ⊣ T ⊗ -`, for the associator as projection map, is the
associator. -/
lemma projectionTensorMap_tensorLeftAdjunction (T : E) [HasRightDual T] (M N : E) :
    (tensorLeftAdjunction T Tᘁ).projectionTensorMap (F := 𝟭 E)
      (fun M N ↦ (α_ Tᘁ M N).hom) M N = (α_ T M N).hom := by
  apply ext_of_comp_counit (adj := tensorLeftAdjunction T Tᘁ)
  rw [map_projectionTensorMap_comp_counit, tensorLeftAdjunction_counit_app',
    tensorLeftAdjunction_counit_app']
  dsimp
  rw [IsIso.Iso.inv_hom]
  monoidal

/-- **Tensoring with a dualizable object.** If the Künneth map of `ev` at `S` is an
isomorphism, then so is the one at `T ⊗ S` for `T` with a right dual: this is the transport of
the Künneth map along the adjunction `Tᘁ ⊗ - ⊣ T ⊗ -`. -/
theorem isIso_pairingKunnethMap_tensor_left {A D W : E} (ev : D ⊗ A ⟶ W) (T : E) [HasRightDual T]
    (S : E) [IsIso (pairingKunnethMap ev S)] : IsIso (pairingKunnethMap ev (T ⊗ S)) := by
  have hπ : ∀ {M M' : E} (φ : M ⟶ M') (N : E),
      (tensorLeft Tᘁ).map φ ▷ N ≫ (α_ Tᘁ M' N).hom =
        (α_ Tᘁ M N).hom ≫ (tensorLeft Tᘁ).map (φ ▷ (𝟭 E).obj N) := fun φ N ↦ by
    simp
  have hπr : ∀ (M : E) {N N' : E} (φ : N ⟶ N'),
      (tensorLeft Tᘁ).obj M ◁ φ ≫ (α_ Tᘁ M N').hom =
        (α_ Tᘁ M N).hom ≫ (tensorLeft Tᘁ).map (M ◁ (𝟭 E).map φ) := fun M N N' φ ↦ by
    simp
  have hassoc : ∀ (M N N' : E), (α_ Tᘁ M N).hom ▷ N' ≫ (α_ Tᘁ (M ⊗ (𝟭 E).obj N) N').hom ≫
      (tensorLeft Tᘁ).map (α_ M ((𝟭 E).obj N) ((𝟭 E).obj N')).hom =
        (α_ _ N N').hom ≫ (α_ Tᘁ M (N ⊗ N')).hom ≫
          (tensorLeft Tᘁ).map (M ◁ 𝟙 ((𝟭 E).obj (N ⊗ N'))) := fun M N N' ↦ by
    dsimp
    monoidal
  have hτ (M N : E) : IsIso ((tensorLeftAdjunction T Tᘁ).projectionTensorMap (F := 𝟭 E)
      (fun M N ↦ (α_ Tᘁ M N).hom) M N) := by
    rw [projectionTensorMap_tensorLeftAdjunction]; infer_instance
  have := hτ S D
  have := hτ S W
  have h := (tensorLeftAdjunction T Tᘁ).isIso_map_pairingKunnethMap_iff (F := 𝟭 E)
    (fun M N ↦ (α_ Tᘁ M N).hom) hπ hπr (fun N N' ↦ 𝟙 _) hassoc ev S
  convert h.1 inferInstance using 2 <;> first | rfl | simp

end Dualizable

end CategoryTheory
