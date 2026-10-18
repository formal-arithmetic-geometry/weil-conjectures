/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.FiniteType
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.LimitSquares
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.SepClosedPoint
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.Vanishing.Approximation
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.Vanishing.Limit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

/-!
# Vanishing of higher direct images along a geometric point of the base

Let `K` be a field, `Λ` a finite ring whose exponent is invertible in `K`, `X` a scheme locally
of finite type over `K`, `S''` an affine `K`-scheme and `t : Spec K' ⟶ S''` with `K'` separably
closed. For the projection `h : X ×_K Spec K' ⟶ X ×_K S''` the higher direct images
`R^q h_* (Λ/dΛ)` vanish for `q ≥ 1`
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_field`).

This is blueprint `lem-kun-0f1i-normal` (without the normality hypothesis, which the argument
does not use). The question is local on `X`, so `X` may be assumed affine. Writing `S''` and
`Spec K'` as limits of spectra of finitely generated `K`-algebras, the base-change maps of the
finite-type stages are isomorphisms
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_finiteType`), hence so is the one of
the limit (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`, blueprint
`lem-kun-0ezt`), whose source `p⁻¹ R^q t_* (Λ/dΛ)` vanishes
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isSepClosed`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The affine case of `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_field`: for `X`
affine of finite type over a field `K`, affine `K`-schemes `S`, `T` and `t : T ⟶ S`, the
base-change maps of the square

```
Y ----e---> T
|           |
h           t
v           v
X ×_K S --> S
```

at the constant sheaf `Λ/dΛ` are isomorphisms. Writing `S` and `T` as limits of affine schemes
of finite type over `K` (`AlgebraicGeometry.Scheme.exists_isLimit_finiteType_of_isAffine`),
`t` as the limit of a compatible system of morphisms between them
(`AlgebraicGeometry.exists_eq_isLimitMap_whisker`), this is
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_constantModSheaf_of_isLimit`. -/
theorem Etale.isIso_baseChangeHomologyMap_constantModSheaf_of_isAffine [Finite Λ] {K : Type u}
    [Field K] [HasInvertibleExponent Λ (Spec (.of K))] {X S X' T Y : Scheme.{u}} [IsAffine X]
    [IsAffine S] [IsAffine T] (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX]
    (aS : S ⟶ Spec (.of K)) (b : X' ⟶ X) (p : X' ⟶ S) (hb : IsPullback b p aX aS)
    (t : T ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X') (sq : IsPullback e h t p) (d : ℕ) (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q (Etale.constantModSheaf Λ T d)) := by
  obtain ⟨IS, _, _, DS, tS, πS, ⟨hcS⟩, hDS, hDSmap, htS, hπS⟩ :=
    Scheme.exists_isLimit_finiteType_of_isAffine aS
  obtain ⟨IT, _, _, DT, tT, πT, ⟨hcT⟩, hDT, hDTmap, htT, hπT⟩ :=
    Scheme.exists_isLimit_finiteType_of_isAffine (t ≫ aS)
  have := hDS
  have := hDT
  have := htS
  have := htT
  have (i j : IS) (φ : i ⟶ j) : IsAffineHom (DS.map φ) := hDSmap φ
  have (i j : IT) (φ : i ⟶ j) : IsAffineHom (DT.map φ) := hDTmap φ
  obtain ⟨J, _, _, G, G', _, _, g, hgt, hg⟩ := exists_eq_isLimitMap_whisker (S := Spec (.of K))
    DT tT (Cone.mk T πT) hcT DS tS (Cone.mk S πS) hcS t fun i i' ↦ by
      rw [hπT, hπS]
  have : IsAffine ((Cone.mk T πT).whisker G).pt := inferInstanceAs (IsAffine T)
  have : IsAffine ((Cone.mk S πS).whisker G').pt := inferInstanceAs (IsAffine S)
  exact Etale.isIso_baseChangeHomologyMap_constantModSheaf_of_isLimit Λ (G ⋙ DT) (G' ⋙ DS)
    (fun j ↦ hDT (G.obj j)) (fun j ↦ hDS (G'.obj j)) (fun φ ↦ hDTmap (G.map φ))
    (fun φ ↦ hDSmap (G'.map φ)) (Functor.whiskerLeft G tT) (Functor.whiskerLeft G' tS)
    (fun j ↦ inferInstanceAs (LocallyOfFiniteType (tT.app (G.obj j))))
    (fun j ↦ inferInstanceAs (LocallyOfFiniteType (tS.app (G'.obj j)))) g hg
    ((Cone.mk T πT).whisker G)
    ((Functor.Initial.isLimitWhiskerEquiv G _).symm hcT) ((Cone.mk S πS).whisker G')
    ((Functor.Initial.isLimitWhiskerEquiv G' _).symm hcS) aS (fun j ↦ hπS (G'.obj j)) t
    (fun j ↦ by rw [hgt, IsLimit.map_π]) aX b p hb e h sq d q

/-- Blueprint `lem-kun-0f1i-normal`: for `X` locally of finite type over a field `K`, an affine
`K`-scheme `S''`, a separably closed field `K'` with `t : Spec K' ⟶ S''`, and the projection
`h : X ×_K Spec K' ⟶ X ×_K S''`, the higher direct images `R^q h_* (Λ/dΛ)` vanish for
`q ≥ 1`. -/
theorem Etale.isZero_higherDirectImage_of_field [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X S X' Y : Scheme.{u}} [IsAffine S]
    (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX] (aS : S ⟶ Spec (.of K))
    (b : X' ⟶ X) (p : X' ⟶ S) (_hb : IsPullback b p aX aS)
    {K' : Type u} [Field K'] [IsSepClosed K'] (t : Spec (.of K') ⟶ S)
    (e : Y ⟶ Spec (.of K')) (h : Y ⟶ X') (_sq : IsPullback e h t p) (d : ℕ) {q : ℤ}
    (_hq : 1 ≤ q) :
    IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) := by
  refine Etale.isZero_higherDirectImage_of_isIso_baseChangeHomologyMap Λ _sq q d
    (Etale.isZero_higherDirectImage_of_isSepClosed Λ t d _hq) ?_
  refine Etale.isIso_baseChangeHomologyMap_of_etale_cover Λ (ι := X.affineOpens)
    (fun U ↦ (b ⁻¹ᵁ U.1).ι) (fun x ↦ ?_) (fun U ↦ (b ⁻¹ᵁ U.1).ι ≫ p) (fun _ ↦ 𝟙 S)
    (fun _ ↦ Category.comp_id _) (fun _ ↦ 𝟙 _) (fun _ ↦ t) (fun _ ↦ IsPullback.id_horiz t)
    (fun U ↦ pullback.fst t ((b ⁻¹ᵁ U.1).ι ≫ p)) (fun U ↦ pullback.snd t ((b ⁻¹ᵁ U.1).ι ≫ p))
    (fun U ↦ IsPullback.of_hasPullback _ _) _sq q _ fun U ↦ ?_
  · obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (U := ⊤) (x := b x) trivial
    exact ⟨⟨U, hU⟩, ⟨x, hxU⟩, rfl⟩
  · have : IsAffine U.1.toScheme := U.2
    rw [Etale.isIso_baseChangeHomologyMap_iff_of_iso Λ _ q
      (Etale.upperStarConstantModSheafIso Λ (𝟙 _) d)]
    exact Etale.isIso_baseChangeHomologyMap_constantModSheaf_of_isAffine Λ (U.1.ι ≫ aX) aS
      (b ∣_ U.1) ((b ⁻¹ᵁ U.1).ι ≫ p) ((isPullback_morphismRestrict b U.1).paste_vert _hb) t _ _
      (IsPullback.of_hasPullback _ _) d q

end AlgebraicGeometry
