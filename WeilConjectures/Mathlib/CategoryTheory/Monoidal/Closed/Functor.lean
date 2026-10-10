/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Closed monoidal functors and the projection formula

Let `F : C ⥤ D` be a lax monoidal functor between monoidal closed categories, with a left
adjoint `L ⊣ F`. The *Frobenius map* `L (F K ⊗ M) ⟶ K ⊗ L M`
(`CategoryTheory.Adjunction.frobeniusMap`) is the transpose of
`F K ⊗ M ⟶ F K ⊗ F (L M) ⟶ F (K ⊗ L M)`. This is the monoidal version of
`CategoryTheory.frobeniusMorphism`, as asked for in the TODO of
`Mathlib.CategoryTheory.Monoidal.Closed.Functor`. If it is an isomorphism (the *projection
formula* for `L`), then `F` preserves internal homs: the comparison
`F [K, Z] ⟶ [F K, F Z]` of `CategoryTheory.Functor.LaxMonoidal.ihomComparison` is an
isomorphism (`CategoryTheory.Adjunction.isIso_ihomComparison_app_of_isIso_frobeniusMap`).

For a monoidal functor `F` the comparison maps also transport the canonical map
`[X, 𝟙] ⊗ Z ⟶ [X, Z]` of `CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`
(`CategoryTheory.Functor.Monoidal.map_ihomUnitTensorToIhom_comp_ihomComparison`). Since an
object `X` is dualizable exactly when `[X, 𝟙] ⊗ X ⟶ [X, X]` is an isomorphism, this shows
that dualizability can be tested after applying a jointly conservative family of monoidal
functors preserving internal homs
(`CategoryTheory.MonoidalClosed.isIso_ihomUnitTensorToIhom_of_jointlyReflectIsomorphisms`).

## Main definitions and results

- `CategoryTheory.Adjunction.frobeniusMap`: the Frobenius map `L (F K ⊗ M) ⟶ K ⊗ L M`.
- `CategoryTheory.Adjunction.isIso_ihomComparison_app_of_isIso_frobeniusMap`: the projection
  formula implies that `F` preserves internal homs.
- `CategoryTheory.Adjunction.isIso_frobeniusMap_of_isIso_ihomComparison`: conversely, if `F`
  preserves internal homs, the projection formula holds.
- `CategoryTheory.Functor.Monoidal.isIso_map_ihomUnitTensorToIhom`: a monoidal functor
  preserving the internal homs out of `X` sends `[X, 𝟙] ⊗ X ⟶ [X, X]` to an isomorphism when
  `F X` has a left dual.
- `CategoryTheory.MonoidalClosed.isIso_ihomUnitTensorToIhom_of_jointlyReflectIsomorphisms`:
  the local-to-global principle for dualizability.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory MonoidalClosed CategoryTheory.Functor

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {L : D ⥤ C} {F : C ⥤ D} (adj : L ⊣ F) [F.LaxMonoidal]

/-- The *Frobenius map* `L (F K ⊗ M) ⟶ K ⊗ L M` of an adjunction `L ⊣ F` whose right adjoint
is lax monoidal: the transpose along `L ⊣ F` of
```
F K ⊗ M --(F K ◁ η)--> F K ⊗ F (L M) --μ--> F (K ⊗ L M).
```
It is an isomorphism when the *projection formula* holds for `L`. -/
noncomputable def frobeniusMap (K : C) (M : D) : L.obj (F.obj K ⊗ M) ⟶ K ⊗ L.obj M :=
  (adj.homEquiv _ _).symm (F.obj K ◁ adj.unit.app M ≫ LaxMonoidal.μ F K (L.obj M))

/-- The transpose of the Frobenius map along `L ⊣ F`. -/
lemma homEquiv_frobeniusMap (K : C) (M : D) :
    adj.homEquiv _ _ (adj.frobeniusMap K M) =
      F.obj K ◁ adj.unit.app M ≫ LaxMonoidal.μ F K (L.obj M) :=
  Equiv.apply_symm_apply _ _

@[reassoc]
lemma unit_app_comp_map_frobeniusMap (K : C) (M : D) :
    adj.unit.app _ ≫ F.map (adj.frobeniusMap K M) =
      F.obj K ◁ adj.unit.app M ≫ LaxMonoidal.μ F K (L.obj M) := by
  exact (adj.homEquiv_unit _ _ _).symm.trans (adj.homEquiv_frobeniusMap K M)

/-- The Frobenius map is natural in the second variable. -/
@[reassoc]
lemma map_whiskerLeft_comp_frobeniusMap (K : C) {M M' : D} (m : M ⟶ M') :
    L.map (F.obj K ◁ m) ≫ adj.frobeniusMap K M' = adj.frobeniusMap K M ≫ K ◁ L.map m := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, homEquiv_frobeniusMap,
    homEquiv_frobeniusMap, Category.assoc, ← LaxMonoidal.μ_natural_right,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← adj.unit_naturality]

/-- The Frobenius map is natural in the first variable. -/
@[reassoc]
lemma map_whiskerRight_comp_frobeniusMap {K K' : C} (k : K ⟶ K') (M : D) :
    L.map (F.map k ▷ M) ≫ adj.frobeniusMap K' M = adj.frobeniusMap K M ≫ k ▷ L.obj M := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, homEquiv_frobeniusMap,
    homEquiv_frobeniusMap, Category.assoc, ← LaxMonoidal.μ_natural_left, ← whisker_exchange_assoc]
  rfl

variable [MonoidalClosed C] [MonoidalClosed D]

/-- The transpose of `y : K ⊗ L M ⟶ Z` along `L ⊣ F`, followed by the comparison map
`F [K, Z] ⟶ [F K, F Z]`, is the transpose of the Frobenius map followed by `y`. -/
lemma uncurry_homEquiv_curry_comp_ihomComparison (K Z : C) (M : D) (y : K ⊗ L.obj M ⟶ Z) :
    uncurry (adj.homEquiv _ _ (curry y) ≫ (LaxMonoidal.ihomComparison F K).natTrans.app Z) =
      adj.homEquiv _ _ (adj.frobeniusMap K M ≫ y) := by
  rw [uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc, LaxMonoidal.ihomComparison_ev,
    adj.homEquiv_unit, adj.homEquiv_naturality_right, homEquiv_frobeniusMap,
    MonoidalCategory.whiskerLeft_comp_assoc, LaxMonoidal.μ_natural_right_assoc, ← F.map_comp,
    ← uncurry_eq, uncurry_curry, Category.assoc]

/-- **The projection formula implies that `F` preserves internal homs.** If the Frobenius map
`L (F K ⊗ M) ⟶ K ⊗ L M` is an isomorphism for every `M`, then the comparison
`F [K, Z] ⟶ [F K, F Z]` is an isomorphism for every `Z`: for every `M`, postcomposition with it
is the composite of the bijections
```
(M ⟶ F [K, Z]) ≃ (L M ⟶ [K, Z]) ≃ (K ⊗ L M ⟶ Z) ≃ (L (F K ⊗ M) ⟶ Z)
  ≃ (F K ⊗ M ⟶ F Z) ≃ (M ⟶ [F K, F Z]).
``` -/
theorem isIso_ihomComparison_app_of_isIso_frobeniusMap (K : C)
    (h : ∀ M, IsIso (adj.frobeniusMap K M)) (Z : C) :
    IsIso ((LaxMonoidal.ihomComparison F K).natTrans.app Z) := by
  refine isIso_of_yoneda_map_bijective _ fun M ↦ ?_
  have he : (fun x : M ⟶ F.obj ((ihom K).obj Z) ↦
      x ≫ (LaxMonoidal.ihomComparison F K).natTrans.app Z) =
      curry ∘ adj.homEquiv _ _ ∘ (adj.frobeniusMap K M ≫ ·) ∘ uncurry ∘
        (adj.homEquiv _ _).symm := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply,
      ← uncurry_homEquiv_curry_comp_ihomComparison, curry_uncurry, curry_uncurry,
      Equiv.apply_symm_apply]
  have hb : Function.Bijective (adj.frobeniusMap K M ≫ · : (K ⊗ L.obj M ⟶ Z) → _) :=
    ⟨fun _ _ hy ↦ (cancel_epi _).1 hy, fun y ↦ ⟨inv (adj.frobeniusMap K M) ≫ y, by simp⟩⟩
  refine (congrArg Function.Bijective he).mpr ?_
  exact ((ihom.adjunction (F.obj K)).homEquiv _ _).bijective.comp <|
    (adj.homEquiv _ _).bijective.comp <| hb.comp <|
      ((ihom.adjunction K).homEquiv _ _).symm.bijective.comp (adj.homEquiv _ _).symm.bijective

/-- **Preservation of internal homs implies the projection formula.** If the comparison
`F [K, Z] ⟶ [F K, F Z]` is an isomorphism for every `Z`, then the Frobenius map
`L (F K ⊗ M) ⟶ K ⊗ L M` is an isomorphism for every `M`: precomposition with it is, up to the
bijections of the adjunctions, postcomposition with the comparison maps. -/
theorem isIso_frobeniusMap_of_isIso_ihomComparison (K : C)
    (h : ∀ Z, IsIso ((LaxMonoidal.ihomComparison F K).natTrans.app Z)) (M : D) :
    IsIso (adj.frobeniusMap K M) := by
  refine isIso_of_coyoneda_map_bijective _ fun Z ↦ ?_
  have he : (fun y : K ⊗ L.obj M ⟶ Z ↦ adj.frobeniusMap K M ≫ y) =
      (adj.homEquiv _ _).symm ∘ uncurry ∘
        (· ≫ (LaxMonoidal.ihomComparison F K).natTrans.app Z) ∘ adj.homEquiv _ _ ∘ curry := by
    funext y
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply,
      uncurry_homEquiv_curry_comp_ihomComparison, Equiv.symm_apply_apply]
  have hb : Function.Bijective
      (· ≫ (LaxMonoidal.ihomComparison F K).natTrans.app Z : (M ⟶ F.obj ((ihom K).obj Z)) → _) :=
    ⟨fun _ _ hx ↦ (cancel_mono _).1 hx,
      fun x ↦ ⟨x ≫ inv ((LaxMonoidal.ihomComparison F K).natTrans.app Z), by simp⟩⟩
  refine (congrArg Function.Bijective he).mpr ?_
  exact (adj.homEquiv _ _).symm.bijective.comp <|
    ((ihom.adjunction (F.obj K)).homEquiv _ _).symm.bijective.comp <| hb.comp <|
      (adj.homEquiv _ _).bijective.comp ((ihom.adjunction K).homEquiv _ _).bijective

/-- The Frobenius maps of `L ⊣ F` at `K` are isomorphisms exactly when `F` preserves the
internal homs out of `K`. -/
theorem isIso_frobeniusMap_iff (K : C) :
    (∀ M, IsIso (adj.frobeniusMap K M)) ↔
      ∀ Z, IsIso ((LaxMonoidal.ihomComparison F K).natTrans.app Z) :=
  ⟨adj.isIso_ihomComparison_app_of_isIso_frobeniusMap K,
    adj.isIso_frobeniusMap_of_isIso_ihomComparison K⟩

end Adjunction

namespace Functor.Monoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (F : C ⥤ D) [F.Monoidal]

/-- A monoidal functor transports the canonical map `[X, 𝟙] ⊗ Z ⟶ [X, Z]` through its
internal-hom comparison maps: the square
```
       F ([X, 𝟙] ⊗ Z) ───────── F (ihomUnitTensorToIhom X Z) ─────────▶ F [X, Z]
            │                                                             │
   δ ≫ (c ≫ [F X, η]) ▷ F Z                                               │ c
            ▼                                                             ▼
   [F X, 𝟙] ⊗ F Z ──────── ihomUnitTensorToIhom (F X) (F Z) ─────────▶ [F X, F Z]
```
commutes, where `c` is `CategoryTheory.Functor.LaxMonoidal.ihomComparison`. -/
lemma map_ihomUnitTensorToIhom_comp_ihomComparison (X Z : C) :
    F.map (ihomUnitTensorToIhom X Z) ≫ (LaxMonoidal.ihomComparison F X).natTrans.app Z =
      OplaxMonoidal.δ F _ _ ≫
        ((LaxMonoidal.ihomComparison F X).natTrans.app (𝟙_ C) ≫
          (ihom (F.obj X)).map (OplaxMonoidal.η F)) ▷ F.obj Z ≫
        ihomUnitTensorToIhom (F.obj X) (F.obj Z) := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    LaxMonoidal.ihomComparison_ev, LaxMonoidal.μ_natural_right_assoc, ← F.map_comp,
    whiskerLeft_ihomUnitTensorToIhom_ev, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_ihomUnitTensorToIhom_ev,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, ihom.ev_naturality,
    LaxMonoidal.ihomComparison_ev_assoc, ← cancel_epi (F.obj X ◁ LaxMonoidal.μ F _ _),
    ← MonoidalCategory.whiskerLeft_comp_assoc, Monoidal.μ_δ, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]
  simp

/-- If `F` preserves the internal homs out of `X` and `F X` has a left dual, then `F` sends
the canonical map `[X, 𝟙] ⊗ X ⟶ [X, X]` to an isomorphism. -/
theorem isIso_map_ihomUnitTensorToIhom (X : C)
    (hc : ∀ Z, IsIso ((LaxMonoidal.ihomComparison F X).natTrans.app Z))
    (Y : D) [ExactPairing Y (F.obj X)] :
    IsIso (F.map (ihomUnitTensorToIhom X X)) := by
  have := isIso_ihomUnitTensorToIhom Y (F.obj X) (F.obj X)
  have h := map_ihomUnitTensorToIhom_comp_ihomComparison F X X
  have : IsIso (F.map (ihomUnitTensorToIhom X X) ≫
      (LaxMonoidal.ihomComparison F X).natTrans.app X) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((LaxMonoidal.ihomComparison F X).natTrans.app X)

end Functor.Monoidal

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/-- **Dualizability is local.** Let `F i : C ⥤ D i` be a family of monoidal functors between
monoidal closed categories which jointly reflect isomorphisms. If every `F i` preserves the
internal homs out of `X` and every `F i X` has a left dual, then the canonical map
`[X, 𝟙] ⊗ X ⟶ [X, X]` is an isomorphism, so that `[X, 𝟙]` is a left dual of `X`
(`CategoryTheory.MonoidalClosed.exactPairingOfIsIso`). -/
theorem isIso_ihomUnitTensorToIhom_of_jointlyReflectIsomorphisms {ι : Type*}
    {D : ι → Type*} [∀ i, Category* (D i)] [∀ i, MonoidalCategory (D i)]
    [∀ i, MonoidalClosed (D i)] (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (hF : ∀ ⦃A B : C⦄ (f : A ⟶ B), (∀ i, IsIso ((F i).map f)) → IsIso f) (X : C)
    (hc : ∀ i Z, IsIso ((Functor.LaxMonoidal.ihomComparison (F i) X).natTrans.app Z))
    (hX : ∀ i, ∃ Y : D i, Nonempty (ExactPairing Y ((F i).obj X))) :
    IsIso (ihomUnitTensorToIhom X X) :=
  hF _ fun i ↦ by
    obtain ⟨Y, ⟨_⟩⟩ := hX i
    exact Functor.Monoidal.isIso_map_ihomUnitTensorToIhom (F i) X (hc i) Y

end MonoidalClosed

end CategoryTheory
