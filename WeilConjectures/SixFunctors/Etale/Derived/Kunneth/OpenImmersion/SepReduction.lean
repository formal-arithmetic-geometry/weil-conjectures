/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldExtensionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Torsion

/-!
# Reduction to a separably closed ground field

Let `K` be a field, `j : U ⟶ X` an open immersion of `K`-schemes, `q₁ : W ⟶ X` a morphism and
`V = U ×_X W`, with projections `e : V ⟶ U` and `h : V ⟶ W`. For a field extension `L / K`
(for instance a separable closure of `K`), the base change map of this square is an isomorphism
as soon as the one of its base change along `Spec L ⟶ Spec K` is
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIso_fieldExtension`).

## Implementation details

Base change along `Spec L ⟶ Spec K` gives a cube whose side faces satisfy base change (base change
along field extensions). By the compatibility of base change maps with further base change and
the conservativity of the pullback along the surjective morphism `W_L ⟶ W`, the result follows.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Reduction to a separably closed ground field.** Let `j : U ⟶ X` be a quasi-compact open
immersion over a field `K`, `q₁ : W ⟶ X`, `V = U ×_X W` (the square `sq`), `L / K` a field
extension and `sq'` the base change of `sq` to `L`. Let `n` be invertible in `K` and kill `Λ`. If
the degree-`i` base change map of `sq'` at the pullback `F_L` of `F` is an isomorphism, then so is
the degree-`i` base change map `q₁⁻¹ R^i j_* F ⟶ R^i h_* e⁻¹ F` of `sq` at `F`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isIso_fieldExtension {K L : Type u} [Field K]
    [Field L] [Algebra K L] {X U W V X' U' W' V' : Scheme.{u}} (aX : X ⟶ Spec (.of K))
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (q₁ : W ⟶ X) (e : V ⟶ U) (h : V ⟶ W)
    (sq : IsPullback e h j q₁) (u : X' ⟶ X) (aX' : X' ⟶ Spec (.of L))
    (hX : IsPullback u aX' aX (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (uU : U' ⟶ U) (j' : U' ⟶ X') (hU : IsPullback uU j' j u)
    (uW : W' ⟶ W) (q₁' : W' ⟶ X') (hW : IsPullback uW q₁' q₁ u)
    (uV : V' ⟶ V) (e' : V' ⟶ U') (h' : V' ⟶ W') (hV : IsPullback uV h' h uW)
    (sq' : IsPullback e' h' j' q₁') (he : e' ≫ uU = uV ≫ e) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (i : ℤ) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : IsIso (Etale.baseChangeHomologyMap Λ sq' i ((uU)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq i F) := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hnK : (n : K) ≠ 0 := hn.ne_zero
  have := Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero n hn₀ hΛ hnK F
  have := Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero n hn₀ hΛ hnK
    ((e)^*[ModuleCat.{u + 1} Λ].obj F)
  have : QuasiCompact h := MorphismProperty.of_isPullback sq ‹QuasiCompact j›
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq inferInstance
  have hsurj : Surjective uW := by
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
      ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
    have : Surjective u := MorphismProperty.of_isPullback hX.flip this
    exact MorphismProperty.of_isPullback hW.flip this
  exact Etale.isIso_baseChangeHomologyMap_of_cube_of_surjective Λ sq hU sq' hV hW.w.symm he
    hsurj.surj i F
    (Etale.isIso_baseChangeHomologyMap_of_fieldExtension Λ aX j u aX' hX hU i F)
    (Etale.isIso_baseChangeHomologyMap_of_fieldExtension Λ (q₁ ≫ aX) h uW (q₁' ≫ aX')
      (hW.paste_vert hX) hV i _) H

end AlgebraicGeometry
