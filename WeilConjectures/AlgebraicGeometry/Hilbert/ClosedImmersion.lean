/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# The Hilbert functor of a closed subscheme

Let `i : X ⟶ Y` be a closed immersion and `g : Y ⟶ S`. Pushing closed subschemes forward along
the closed immersions `X ×[S] T ⟶ Y ×[S] T` identifies `Hilb^d_{X/S}` with the subfunctor of
`Hilb^d_{Y/S}` of those `Z ⊆ Y_T` contained in `X_T`. We show that this subfunctor is closed:
for an affine `T` and `Z ∈ Hilb^d_{Y/S}(T)` there is a largest closed subscheme `T_X ⊆ T` over
which `Z` lies in `X_T` (the *closed-immersion claim*, blueprint `lem-pc-hilb-representable`,
Step 1). Consequently, if `Hilb^d_{Y/S}` is representable, so is `Hilb^d_{X/S}`.

## Main definitions

- `AlgebraicGeometry.pullbackCompMap`: the closed immersion `X ×[S] T ⟶ Y ×[S] T`.
- `AlgebraicGeometry.hilbertPresheafCompι`: the inclusion `Hilb^d_{X/S} ⟶ Hilb^d_{Y/S}`.

## Main statements

- `AlgebraicGeometry.exists_le_ker_iff_mem_range_hilbertPresheafCompι`: the closed-immersion
  claim, for an affine base `T`.
- `AlgebraicGeometry.isRepresentable_hilbertPresheaf_of_isClosedImmersion`: if `Hilb^d_{Y/S}`
  is representable, so is `Hilb^d_{X/S}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ S)

/-- For a closed immersion `i : X ⟶ Y` over `S` and an `S`-scheme `T`, the closed immersion
`X ×[S] T ⟶ Y ×[S] T`. -/
noncomputable abbrev pullbackCompMap (T : Over S) :
    pullback (i ≫ g) T.hom ⟶ pullback g T.hom :=
  pullback.map _ _ _ _ i (𝟙 _) (𝟙 _) (by simp) (by simp)

instance (T : Over S) : IsClosedImmersion (pullbackCompMap i g T) :=
  sorry

/-- **`Hilb^d_{X/S}` is a subfunctor of `Hilb^d_{Y/S}`.** For a closed immersion `i : X ⟶ Y`,
pushing forward closed subschemes along the closed immersions `X ×[S] T ⟶ Y ×[S] T` is a
natural transformation `Hilb^d_{X/S} ⟶ Hilb^d_{Y/S}`. -/
noncomputable def hilbertPresheafCompι (d : ℕ) :
    hilbertPresheaf (i ≫ g) d ⟶ hilbertPresheaf g d where
  app T := TypeCat.ofHom fun J ↦ ⟨J.1.map (pullbackCompMap i g T.unop), sorry⟩
  naturality := sorry

lemma hilbertPresheafCompι_app_coe (d : ℕ) {T : Over S}
    (J : (hilbertPresheaf (i ≫ g) d).obj (op T)) :
    ((hilbertPresheafCompι i g d).app (op T) J).1 = J.1.map (pullbackCompMap i g T) :=
  rfl

/-- The inclusion `Hilb^d_{X/S} ⟶ Hilb^d_{Y/S}` is injective. -/
lemma hilbertPresheafCompι_app_injective (d : ℕ) (T : Over S) :
    Function.Injective ((hilbertPresheafCompι i g d).app (op T)) :=
  sorry

/-- A point `Z` of `Hilb^d_{Y/S}(T)` comes from `Hilb^d_{X/S}(T)` if and only if `Z ⊆ X_T`. -/
lemma exists_hilbertPresheafCompι_app_eq_iff (d : ℕ) {T : Over S}
    (I : (hilbertPresheaf g d).obj (op T)) :
    (∃ J, (hilbertPresheafCompι i g d).app (op T) J = I) ↔
      (pullbackCompMap i g T).ker ≤ I.1 :=
  sorry

/-- **The closed-immersion claim** (blueprint `lem-pc-hilb-representable`, Step 1). For a closed
immersion `i : X ⟶ Y`, an affine `S`-scheme `T` and `Z ∈ Hilb^d_{Y/S}(T)`, there is a closed
subscheme `T_X ⊆ T`, given by its ideal sheaf `K`, such that for every affine `W` over `T` the
pullback `Z_W` lies in `X_W` if and only if `W ⟶ T` factors through `T_X`. -/
theorem exists_le_ker_iff_mem_range_hilbertPresheafCompι (d : ℕ) (T : Over S)
    [IsAffine T.left] (z : (hilbertPresheaf g d).obj (op T)) :
    ∃ K : T.left.IdealSheafData, ∀ (W : Over S) [IsAffine W.left] (a : W ⟶ T),
      (∃ x, (hilbertPresheafCompι i g d).app (op W) x = (hilbertPresheaf g d).map a.op z) ↔
        K ≤ a.left.ker :=
  sorry

/-- **The closed-immersion claim, representability** (blueprint `lem-pc-hilb-representable`,
Step 1). For a closed immersion `i : X ⟶ Y` and `g : Y ⟶ S`, the functor `Hilb^d_{X/S}` is a
closed subfunctor of `Hilb^d_{Y/S}`; in particular, if `Hilb^d_{Y/S}` is representable, so is
`Hilb^d_{X/S}`, by a closed subscheme. -/
theorem isRepresentable_hilbertPresheaf_of_isClosedImmersion (d : ℕ)
    (hg : (hilbertPresheaf g d).IsRepresentable) :
    (hilbertPresheaf (i ≫ g) d).IsRepresentable :=
  sorry

end AlgebraicGeometry
