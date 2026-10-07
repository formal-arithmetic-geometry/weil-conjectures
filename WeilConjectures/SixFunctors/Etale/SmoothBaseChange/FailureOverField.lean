/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

/-!
# A failure of base change is detected over a field

If `BC(p, Λ, q')` holds universally for all `q' < q` but `BC(p, Λ, q)` fails, then the
failure is already visible after base change to an affine open `S' ⊆ S` and over a field:
there is a Cartesian square whose base is the spectrum of a field and a sheaf of `Λ`-modules
on it for which the degree-`q` base-change map is not an isomorphism. The data of such a
counterexample is bundled as `AlgebraicGeometry.Etale.FieldFailure`.

The proof applies `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty` to the
property "the chosen cokernel element survives",
`AlgebraicGeometry.Etale.SurvivesBaseChange`: an element `ξ` of a geometric stalk of
`R^q h_* e⁻¹ F` not in the image of the base-change map is transported along `π : T' ⟶ T` by
the transition maps `AlgebraicGeometry.Etale.baseChangeTargetTransition`, and the property
asks that its image is still not in the image of the base-change map over `T'`. The four
hypotheses of the minimal-counterexample lemma are verified separately: invariance under
thickenings, compatibility with limits, the closed–open splitting (which is where
`AlgebraicGeometry.Etale.mono_cokernelMap` and `AlgebraicGeometry.Etale.mono_cokernelDesc`
enter) and the failure over the empty scheme.

## Main definitions

- `AlgebraicGeometry.Etale.FieldFailure`: a counterexample to `BC(p, Λ, q)` living over a
  field, after an affine base change of `p`.
- `AlgebraicGeometry.Etale.baseChangeTargetTransition`: the map relating the targets of the
  base-change maps over `T` and over `T'`, for `π : T' ⟶ T`.
- `AlgebraicGeometry.Etale.SurvivesBaseChange`: the property "the chosen cokernel element
  survives" of schemes over `T`.

## Main statements

- `AlgebraicGeometry.Etale.isQcqsLocalProperty_survivesBaseChange`: that property satisfies
  the hypotheses of the minimal-counterexample lemma.
- `AlgebraicGeometry.Etale.nonempty_fieldFailure`: if `BC(p, Λ, q')` holds universally for
  `q' < q` and `BC(p, Λ, q)` fails, a counterexample over a field exists.
- `AlgebraicGeometry.Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty`: the same
  conclusion when `BC(p, Λ, q)` only fails after some base change, as in the blueprint.
- `AlgebraicGeometry.Etale.FieldFailure.isAffineHom_a`: if `S` is separated, the base change
  `S' ⟶ S` of such a counterexample is affine.

## References

- Stacks Project, Lemma 59.88.6, <https://stacks.math.columbia.edu/tag/0F07>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section FieldFailure

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- A counterexample to `BC(p, Λ, q)` living over a field: an affine scheme `S'` over `S`,
the base change `p' : X' ⟶ S'` of `p` along it, a field `K` over `S'`, and a sheaf `F`
of `Λ`-modules on `(Spec K)_ét` for which the degree-`q` base-change map of the geometric
fibre square is not an isomorphism. The two squares are stacked:

```
Y' -----e-----> Spec K
|                 |
h                 g
v                 v
X' -----p'-----> S'
|                 |
b                 a
v                 v
X ------p------>  S
```

When `S` is separated the base change `a : S' ⟶ S` is affine, see
`AlgebraicGeometry.Etale.FieldFailure.isAffineHom_a`. -/
structure Etale.FieldFailure (q : ℤ) where
  /-- the affine base of the counterexample -/
  S' : Scheme.{u}
  [isAffine : IsAffine S']
  /-- the base change morphism -/
  a : S' ⟶ S
  /-- the total space of the base change of `p` -/
  X' : Scheme.{u}
  /-- the base change of `p` -/
  p' : X' ⟶ S'
  /-- the morphism covering `a` -/
  b : X' ⟶ X
  /-- `p'` is the base change of `p` along `a` -/
  isPullback : IsPullback b p' p a
  /-- the field over which the failure happens -/
  K : Type u
  [field : Field K]
  /-- the point of `S'` -/
  g : Spec (CommRingCat.of K) ⟶ S'
  /-- the fibre of `p'` over that point -/
  Y' : Scheme.{u}
  /-- the projection of the fibre to the point -/
  e : Y' ⟶ Spec (CommRingCat.of K)
  /-- the projection of the fibre to `X'` -/
  h : Y' ⟶ X'
  /-- the fibre square is Cartesian -/
  isPullback_fibre : IsPullback e h g p'
  /-- the coefficient sheaf witnessing the failure -/
  F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  /-- the base-change map is not an isomorphism -/
  not_isIso : ¬ IsIso (Etale.baseChangeHomologyMap Λ isPullback_fibre q F)

variable {Λ p} in
/-- Blueprint `sbc-lem-bc-failure-field` (last clause): if `S` is separated, the base change
`S' ⟶ S` of a counterexample over a field is affine, since `S'` is affine. -/
lemma Etale.FieldFailure.isAffineHom_a [S.IsSeparated] {q : ℤ} (F : Etale.FieldFailure Λ p q) :
    IsAffineHom F.a :=
  have := F.isAffine
  have : IsAffineHom (F.a ≫ terminal.from S) := by
    rw [terminal.comp_from]
    infer_instance
  IsAffineHom.of_comp F.a (terminal.from S)

end FieldFailure

section Transition

variable {X T Y T' Y' : Scheme.{u}}

/-- The map from the target of the base-change map over `T` to the target of the base-change
map over `T'`, for `π : T' ⟶ T` covered by `a : Y' ⟶ Y` over `X`: `H^q` applied to the
transition map `Rh_*(e^*(F[0])) ⟶ Rh'_*(a^* e^*(F[0])) ≅ Rh'_*(e'^*((π^* F)[0]))` of
`AlgebraicGeometry.Etale.lowerStarPlusTransition`. -/
noncomputable def Etale.baseChangeTargetTransition (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X) (wa : a ≫ e = e' ≫ π)
    (wh : a ≫ h = h') (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.baseChangeTargetFunctor Λ e h q).obj F ⟶
      (Etale.baseChangeTargetFunctor Λ e' h' q).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    (Etale.lowerStarPlusTransition Λ a h h' wh _ ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
          eqToHom (by rw [wa]) ≫
          (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app _ ≫
          D+((e')^*[ModuleCat.{u + 1} Λ]).map
            ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)))

end Transition

section TransitionCompat

variable {X S T Y T' Y' : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- For a commutative square with sides `a`, `a ≫ h`, `h` and `𝟙 X`, the composition isomorphism
`D(a ≫ h)^*⁺ ≅ Dh^*⁺ ⋙ Da^*⁺` is the identity isomorphism of `D(𝟙 X)^*⁺` followed by the
pullback comparison of the square. -/
lemma Etale.upperStarPlusComp_hom_app_eq_pullbackSquareComparison {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    (h : Y ⟶ X) (sq : CommSq a (a ≫ h) h (𝟙 X))
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom.app M =
      D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app M) ≫
        (Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq).hom.app M := by
  rw [Etale.pullbackSquareComparison_eq, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, ← Category.assoc,
    Etale.upperStarCompDerivedPlus_id_right_inv_app, Category.id_comp,
    Etale.upperStarCompDerivedPlus_eq_eqToIso_trans, eqToIso_refl, Iso.refl_trans]

/-- The transition map `Rh_* K ⟶ Rh'_* (a^* K)` of a triangle `a ≫ h = h'` is the derived
base-change map of the degenerate square with sides `a`, `h'`, `h` and `𝟙 X`, preceded by the
identity isomorphism `Rh_* K ≅ (𝟙 X)^* Rh_* K`. -/
lemma Etale.lowerStarPlusTransition_eq_baseChange {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    (h : Y ⟶ X) (h' : Y' ⟶ X) (w : a ≫ h = h') (sq : CommSq a h' h (𝟙 X))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.lowerStarPlusTransition Λ a h h' w K =
      (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app
          (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K := by
  subst w
  rw [Etale.baseChange_app, Etale.baseChangeUnitStep_app, Etale.baseChangeSquareStep_hom_app,
    Etale.baseChangeCounitStep_app, Etale.lowerStarPlusTransition, eqToIso_refl, Iso.refl_trans,
    Etale.upperStarPlusComp_hom_app_eq_pullbackSquareComparison Λ a h sq]
  have hu : (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app
        (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).unit.app
        ((R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K) =
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).unit.app
        (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map (D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app
          (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) :=
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).unit.naturality _
  conv_rhs => rw [← Category.assoc, hu]
  simp only [Functor.map_comp, Category.assoc]

/-- **Compatibility of the base-change map with the transition maps.** For a square `sq` on
`p` along `g`, a morphism `π : T' ⟶ T` and a square `sq'` on `p` along `π ≫ g` covering `π`
through `a`, the derived base-change map of `sq` followed by the transition map of the targets
is the pullback along `p` of the transition map of the sources followed by the derived
base-change map of `sq'`. Both composites are the derived base-change map of the square with
sides `e' ≫ π`, `h'`, `g` and `p`, by the pasting law, once the transition maps are written as
base-change maps of degenerate squares
(`AlgebraicGeometry.Etale.lowerStarPlusTransition_eq_baseChange`). -/
theorem Etale.baseChange_app_comp_lowerStarPlusTransition (sq : CommSq e h g p) (π : T' ⟶ T)
    {e' : Y' ⟶ T'} {h' : Y' ⟶ X} (sq' : CommSq e' h' (π ≫ g) p) (a : Y' ⟶ Y)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K ≫
        Etale.lowerStarPlusTransition Λ a h h' wh (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app K ≫
            eqToHom (by rw [wa]) ≫
            (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app K) =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.lowerStarPlusTransition Λ π g (π ≫ g) rfl K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
          (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  have degT : CommSq a h' h (𝟙 X) := ⟨by rw [wh, Category.comp_id]⟩
  have degS : CommSq π (π ≫ g) g (𝟙 S) := ⟨by rw [Category.comp_id]⟩
  have sqT : CommSq (e' ≫ π) h' g p := ⟨by rw [Category.assoc, sq'.w]⟩
  have h₁ := Etale.baseChange_app_paste_horiz_of_eq Λ sq degT sqT wa (Category.id_comp p) K
  have h₂ := Etale.baseChange_app_paste_horiz_of_eq Λ degS sq' sqT rfl (Category.comp_id p) K
  have hc : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (e' ≫ π) wa.symm).hom.app K ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app K ≫ eqToHom (by rw [wa]) ≫
        (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app K =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (e' ≫ π) rfl).hom.app K := by
    rw [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans,
      Etale.upperStarCompDerivedPlus_eq_eqToIso_trans, eqToIso_refl, Iso.refl_trans,
      Iso.trans_hom, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc, eqToIso.hom,
      eqToHom_app, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h₁' : D+((𝟙 X)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) degT).app (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (𝟙 X) p p
        (Category.id_comp p).symm).inv.app (R+((g)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sqT).app K ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (e' ≫ π)
          wa.symm).hom.app K) := by
    rw [h₁]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
      Iso.inv_hom_id_app_assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h₂' : D+((p)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) degS).app K) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) p (𝟙 S) p
        (Category.comp_id p).symm).inv.app (R+((g)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sqT).app K ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (e' ≫ π) rfl).hom.app K) := by
    rw [h₂]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
      Iso.inv_hom_id_app_assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.naturality
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K)
  rw [Functor.id_map] at hn
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' wh degT,
    Etale.lowerStarPlusTransition_eq_baseChange Λ π g (π ≫ g) rfl degS, Category.assoc,
    reassoc_of% hn]
  erw [reassoc_of% h₁']
  rw [(D+((p)^*[ModuleCat.{u + 1} Λ])).map_comp, Category.assoc, h₂',
    reassoc_of% Etale.upperStarCompDerivedPlus_id_left_inv_app,
    reassoc_of% Etale.upperStarCompDerivedPlus_id_right_inv_app, ← Functor.map_comp, hc]

/-- The map from the source of the base-change map over `T` to the source of the base-change
map over `T'`, for `π : T' ⟶ T`: `H^q` of the pullback along `p` of the transition map
`Rg_*(F[0]) ⟶ R(π ≫ g)_*(π^*(F[0])) ≅ R(π ≫ g)_*((π^* F)[0])` of
`AlgebraicGeometry.Etale.lowerStarPlusTransition`. -/
noncomputable def Etale.baseChangeSourceTransition (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
    (π : T' ⟶ T) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.baseChangeSourceFunctor Λ p g q).obj F ⟶
      (Etale.baseChangeSourceFunctor Λ p (π ≫ g) q).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    (D+((p)^*[ModuleCat.{u + 1} Λ]).map
      (Etale.lowerStarPlusTransition Λ π g (π ≫ g) rfl _ ≫
        R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)))

/- Generic forms of the identifications used below, stated for abstract functors so that their
instances at the concrete derived functors are checked syntactically (see the implementation
notes of `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality`). -/
omit [CommRing Λ] in
private lemma whiskerLeft_whiskerRight_app' {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* 𝒞] [Category* 𝒟] (E : 𝒜 ⥤ ℬ) {P Q : ℬ ⥤ 𝒞} (α : P ⟶ Q) (Hh : 𝒞 ⥤ 𝒟) (X : 𝒜) :
    (Functor.whiskerLeft E (Functor.whiskerRight α Hh)).app X = Hh.map (α.app (E.obj X)) :=
  rfl

omit [CommRing Λ] in
private lemma natTrans_app_comp_map_map_iso_hom_app {𝒜 𝒜' ℬ ℬ' 𝒞 𝒞' 𝒟 : Type*} [Category* 𝒜]
    [Category* 𝒜'] [Category* ℬ] [Category* ℬ'] [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟]
    {E : 𝒜 ⥤ ℬ} {G : ℬ ⥤ ℬ'} {G' : 𝒜 ⥤ 𝒜'} {E' : 𝒜' ⥤ ℬ'} (s : E ⋙ G ≅ G' ⋙ E')
    {P₁ : ℬ' ⥤ 𝒞} {P₂ : 𝒞 ⥤ 𝒟} {Q₁ : ℬ' ⥤ 𝒞'} {Q₂ : 𝒞' ⥤ 𝒟} (β : P₁ ⋙ P₂ ⟶ Q₁ ⋙ Q₂)
    (F : 𝒜) :
    β.app (G.obj (E.obj F)) ≫ Q₂.map (Q₁.map (s.hom.app F)) =
      P₂.map (P₁.map (s.hom.app F)) ≫ β.app (E'.obj (G'.obj F)) :=
  (β.naturality (s.hom.app F)).symm

/-- The form of `AlgebraicGeometry.Etale.baseChange_app_comp_lowerStarPlusTransition` for a
sheaf placed in degree `0`, including the identifications `π^*(F[0]) ≅ (π^* F)[0]`. -/
theorem Etale.baseChange_app_single_comp_transition (sq : IsPullback e h g p)
    (π : T' ⟶ T) {e' : Y' ⟶ T'} {h' : Y' ⟶ X} (sq' : IsPullback e' h' (π ≫ g) p)
    (a : Y' ⟶ Y) (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (Etale.lowerStarPlusTransition Λ a h h' wh _ ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
            eqToHom (by rw [wa]) ≫
            (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app _ ≫
            D+((e')^*[ModuleCat.{u + 1} Λ]).map
              ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))) =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map
          (Etale.lowerStarPlusTransition Λ π g (π ≫ g) rfl _ ≫
            R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).map
              ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq'.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
  have hc := Etale.baseChange_app_comp_lowerStarPlusTransition Λ sq.toCommSq π sq'.toCommSq a
    wa wh ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  simp only [Functor.map_comp, Category.assoc] at hc ⊢
  rw [reassoc_of% hc, natTrans_app_comp_map_map_iso_hom_app]

/-- The degree-`q` base-change maps over `T` and over `T'` commute with the transition maps
`AlgebraicGeometry.Etale.baseChangeSourceTransition` and
`AlgebraicGeometry.Etale.baseChangeTargetTransition`. -/
theorem Etale.baseChangeHomologyMap_comp_baseChangeTargetTransition (sq : IsPullback e h g p)
    (q : ℤ) (π : T' ⟶ T) {e' : Y' ⟶ T'} {h' : Y' ⟶ X} (sq' : IsPullback e' h' (π ≫ g) p)
    (a : Y' ⟶ Y) (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.baseChangeHomologyMap Λ sq q F ≫
        Etale.baseChangeTargetTransition Λ e h q π a e' h' wa wh F =
      Etale.baseChangeSourceTransition Λ p g q π F ≫
        Etale.baseChangeHomologyMap Λ sq' q (((π)^*[ModuleCat.{u + 1} Λ]).obj F) := by
  rw [Etale.baseChangeHomologyMap, Etale.baseChangeHomologyMap,
    Etale.baseChangeHomologyNatTrans_eq, Etale.baseChangeHomologyNatTrans_eq,
    whiskerLeft_whiskerRight_app', whiskerLeft_whiskerRight_app',
    Etale.baseChangeTargetTransition, Etale.baseChangeSourceTransition, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1
  exact Etale.baseChange_app_single_comp_transition Λ sq π sq' a wa wh F

end TransitionCompat

section Survival

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The property "the chosen cokernel element survives" of schemes `π : T' ⟶ T` over `T`.

Fix a Cartesian square `sq` with base `g : T ⟶ S`, a sheaf `F` on `T_ét`, a point `x` of `X`
and an element `ξ` of the stalk of `R^q h_* e⁻¹ F` at the geometric point over `x`. For
`π : T' ⟶ T` let `Y' = T' ×_S X`. The property holds for `π` if the image of `ξ` under the
transition map to the stalk of `R^q h'_* e'⁻¹ π⁻¹ F` is not in the image of the base-change
map of the square over `π ≫ g`. -/
def Etale.SurvivesBaseChange (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    ⦃T' : Scheme.{u}⦄ (π : T' ⟶ T) : Prop :=
  ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeTargetTransition Λ e h q π
        (sq.lift (pullback.fst (π ≫ g) p ≫ π) (pullback.snd (π ≫ g) p)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.fst (π ≫ g) p) (pullback.snd (π ≫ g) p) (sq.lift_fst _ _ _)
        (sq.lift_snd _ _ _) F)).hom ξ ∉
    Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback (π ≫ g) p) q
        (((π)^*[ModuleCat.{u + 1} Λ]).obj F))).hom

variable {Λ}

/-- Along the identity of `T` the transition maps do not change the base-change map: an
element `ξ` not in the image of the base-change map over `T` survives along `𝟙 T`. -/
theorem Etale.survivesBaseChange_id (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    (hξ : ξ ∉ Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ sq q F)).hom) :
    Etale.SurvivesBaseChange Λ q sq F x ξ (𝟙 T) := by
  have hpb := IsPullback.of_hasPullback (𝟙 T ≫ g) p
  let a := sq.lift (pullback.fst (𝟙 T ≫ g) p ≫ 𝟙 T) (pullback.snd (𝟙 T ≫ g) p)
    (by rw [Category.assoc]; exact pullback.condition)
  have hc := Etale.baseChangeHomologyMap_comp_baseChangeTargetTransition Λ sq q (𝟙 T) hpb a
    (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F
  let b : Y ⟶ pullback (𝟙 T ≫ g) p :=
    pullback.lift e h (by rw [Category.id_comp]; exact sq.w)
  have hab : a ≫ b = 𝟙 _ := pullback.hom_ext (by simp [a, b]) (by simp [a, b])
  have hba : b ≫ a = 𝟙 _ := sq.hom_ext (by simp [a, b]) (by simp [a, b])
  have degT : CommSq a (pullback.snd (𝟙 T ≫ g) p) h (𝟙 X) :=
    ⟨by rw [sq.lift_snd, Category.comp_id]⟩
  have hT : IsIso (Etale.baseChangeTargetTransition Λ e h q (𝟙 T) a (pullback.fst (𝟙 T ≫ g) p)
      (pullback.snd (𝟙 T ≫ g) p) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F) := by
    rw [Etale.baseChangeTargetTransition,
      Etale.lowerStarPlusTransition_eq_baseChange Λ a h _ (sq.lift_snd _ _ _) degT]
    have := fun K ↦ Etale.isIso_baseChange_app_of_inverses Λ degT b (𝟙 X) hab hba
      (Category.id_comp _) (Category.id_comp _) K
    infer_instance
  have degS : CommSq (𝟙 T) (𝟙 T ≫ g) g (𝟙 S) := ⟨by rw [Category.comp_id]⟩
  have hS : IsIso (Etale.baseChangeSourceTransition Λ p g q (𝟙 T) F) := by
    rw [Etale.baseChangeSourceTransition,
      Etale.lowerStarPlusTransition_eq_baseChange Λ (𝟙 T) g _ rfl degS]
    have := fun K ↦ Etale.isIso_baseChange_app_of_inverses Λ degS (𝟙 T) (𝟙 S)
      (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) K
    infer_instance
  rintro ⟨η', hη'⟩
  apply hξ
  have hc' := congrArg (fun f ↦ ModuleCat.Hom.hom ((X.uliftPointSmallEtale x).sheafFiber.map f)) hc
  simp only [Functor.map_comp, ModuleCat.hom_comp] at hc'
  refine ⟨(inv ((X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.baseChangeSourceTransition Λ p g q (𝟙 T) F))).hom η', ?_⟩
  apply ((ConcreteCategory.isIso_iff_bijective ((X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.baseChangeTargetTransition Λ e h q (𝟙 T) a (pullback.fst (𝟙 T ≫ g) p)
      (pullback.snd (𝟙 T ≫ g) p) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F))).1
        inferInstance).1
  have h1 := LinearMap.congr_fun hc' ((inv ((X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.baseChangeSourceTransition Λ p g q (𝟙 T) F))).hom η')
  simp only [LinearMap.coe_comp, Function.comp_apply] at h1
  rw [← hη']
  convert h1 using 2
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id,
    LinearMap.id_apply]

/-- Step (1) of blueprint `sbc-lem-bc-failure-field`: the survival of `ξ` is invariant under
thickenings. A thickening does not change the étale site (blueprint
`sbc-lem-thickening-etale-site`, `AlgebraicGeometry.Etale.isEquivalence_upperStar_of_thickening`),
so the transition maps along it are isomorphisms compatible with the base-change maps. -/
theorem Etale.survivesBaseChange_comp_iff_of_surjective (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T₁ T₂ : Scheme.{u}} (i : T₁ ⟶ T₂) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (f₂ : T₂ ⟶ T) :
    Etale.SurvivesBaseChange Λ q sq F x ξ (i ≫ f₂) ↔ Etale.SurvivesBaseChange Λ q sq F x ξ f₂ :=
  sorry

/-- Step (2) of blueprint `sbc-lem-bc-failure-field`: the survival of `ξ` passes to cofiltered
limits along affine transition morphisms. By the limit theorem for higher direct images
(blueprint `sbc-lem-higher-direct-image-limit`,
`AlgebraicGeometry.Etale.higherDirectImage_limit`) the stalks over the limit are the colimits
of the stalks over the stages, on both sides of the base-change map. -/
theorem Etale.survivesBaseChange_of_isLimit [IsAffine S] (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over T)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Cone D) (hc : IsLimit ((Over.forget T).mapCone c))
    (hD : ∀ i, Etale.SurvivesBaseChange Λ q sq F x ξ (D.obj i).hom) :
    Etale.SurvivesBaseChange Λ q sq F x ξ c.pt.hom :=
  sorry

/-- Step (3) of blueprint `sbc-lem-bc-failure-field`: if `ξ` survives over a quasi-compact
quasi-separated `T'` and `Z ⊆ T'` is closed with quasi-compact complement `V`, then `ξ`
survives over `V` or over `Z`. Embed `π⁻¹ F` into `j_* J ⊕ i_* i⁻¹ π⁻¹ F` with `J` injective
on `V`; by `AlgebraicGeometry.Etale.mono_cokernelMap` the image of `ξ` survives in one of the
summands. For the closed summand use the exactness of `i_*`; for the open summand use the
universal base-change property in degrees `< q` for the base change of `p` along `T' ⟶ S`,
the Leray spectral sequence, and `AlgebraicGeometry.Etale.mono_cokernelDesc`. -/
theorem Etale.survivesBaseChange_or_of_isClosedImmersion [IsAffine S] (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q') (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T' Z : Scheme.{u}} [CompactSpace T'] [QuasiSeparatedSpace T'] (f : T' ⟶ T)
    (V : T'.Opens) (hV : IsCompact (V : Set T')) (i : Z ⟶ T') [IsClosedImmersion i]
    (hi : Set.range i.base = (V : Set T')ᶜ) (hf : Etale.SurvivesBaseChange Λ q sq F x ξ f) :
    Etale.SurvivesBaseChange Λ q sq F x ξ (V.ι ≫ f) ∨
      Etale.SurvivesBaseChange Λ q sq F x ξ (i ≫ f) :=
  sorry

/-- Step (4) of blueprint `sbc-lem-bc-failure-field`: nothing survives over the empty scheme,
since there the fibre `T' ×_S X` is empty and `R^q h'_* e'⁻¹ π⁻¹ F` vanishes. -/
theorem Etale.not_survivesBaseChange_of_isEmpty (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T' : Scheme.{u}} (π : T' ⟶ T) [IsEmpty T'] :
    ¬ Etale.SurvivesBaseChange Λ q sq F x ξ π := by
  intro hP
  apply hP
  have : IsEmpty ↥(pullback (π ≫ g) p) :=
    ⟨fun y ↦ isEmptyElim ((pullback.fst (π ≫ g) p).base y)⟩
  have hsheaf (G : Sheaf (pullback (π ≫ g) p).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsZero G := by
    refine (IsZero.iff_id_eq_zero G).2 (IsTerminal.hom_ext ?_ _ _)
    refine IsTerminal.isTerminalOfObj (sheafToPresheaf _ _) _ (Functor.isTerminal fun U ↦ ?_)
    have : IsEmpty U.unop.left :=
      ⟨fun y ↦ isEmptyElim (show ↥(pullback (π ≫ g) p) from U.unop.hom.base y)⟩
    exact Scheme.Etale.isTerminalSectionsOfIsEmpty G U.unop
  have hK (K : DerivedCategory.Plus
      (Sheaf (pullback (π ≫ g) p).smallEtaleTopology (ModuleCat.{u + 1} Λ))) : IsZero K :=
    IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι K
      (DerivedCategory.isZero_of_forall_isZero_homology _ fun _ ↦ hsheaf _)
  have : R+((pullback.snd (π ≫ g) p)_*[ModuleCat.{u + 1} Λ]).IsRightAdjoint :=
    (Etale.derivedUpperStarLowerStarAdjunctionPlus _ _).isRightAdjoint
  have hzero : IsZero ((Etale.baseChangeTargetFunctor Λ (pullback.fst (π ≫ g) p)
      (pullback.snd (π ≫ g) p) q).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F)) :=
    (DerivedCategory.Plus.homologyFunctor _ q).map_isZero
      (R+((pullback.snd (π ≫ g) p)_*[ModuleCat.{u + 1} Λ]).map_isZero (hK _))
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  have : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).IsLeftAdjoint :=
    inferInstance
  have := (ModuleCat.isZero_iff_subsingleton.1
    (((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).map_isZero hzero))
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The property "the chosen cokernel element survives" satisfies the hypotheses of the
minimal-counterexample lemma `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty`. -/
theorem Etale.isQcqsLocalProperty_survivesBaseChange [IsAffine S] (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q') (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ)) :
    T.IsQcqsLocalProperty (Etale.SurvivesBaseChange Λ q sq F x ξ) where
  invariant_under_thickening i _ hi f₂ :=
    Etale.survivesBaseChange_comp_iff_of_surjective q sq F x ξ i hi f₂
  compatible_with_cofilteredLimit D _ _ _ c hc hD :=
    Etale.survivesBaseChange_of_isLimit q sq F x ξ D c hc hD
  of_opens_or_closedComplement f V hV i _ hi hf :=
    Etale.survivesBaseChange_or_of_isClosedImmersion q hq hprev sq F x ξ f V hV i hi hf
  not_of_isEmpty π _ :=
    Etale.not_survivesBaseChange_of_isEmpty q sq F x ξ π

end Survival

variable {X S : Scheme.{u}} {p : X ⟶ S}

variable {Λ} in
/-- A failure of `BC(p, Λ, q)` is already a failure over an affine open of `S`: the
base-change map and the higher direct images are compatible with restriction to an open of
`S`, which is the pullback along an étale morphism, and being an isomorphism of sheaves is
local (`AlgebraicGeometry.Etale.BaseChangeProperty.of_etale_cover`, applied to the cover of
`S` by its affine opens). -/
theorem Etale.exists_isAffineOpen_not_baseChangeProperty {q : ℤ}
    (hfail : ¬ Etale.BaseChangeProperty Λ p q) :
    ∃ U : S.Opens, IsAffineOpen U ∧ ¬ Etale.BaseChangeProperty Λ (pullback.snd p U.ι) q := by
  by_contra! H
  refine hfail (Etale.BaseChangeProperty.of_etale_cover Λ (ι := S.affineOpens)
    (fun U ↦ pullback.fst p U.1.ι) (fun x ↦ ?_) (fun U ↦ pullback.snd p U.1.ι)
    (fun U ↦ U.1.ι) (fun _ ↦ pullback.condition.symm) fun U ↦ H U.1 U.2)
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p x)) isOpen_univ
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p)
    (g := Scheme.Opens.ι (X := S) U) x ⟨p x, hx⟩ rfl
  exact ⟨⟨U, hU⟩, y, hy⟩

variable (p) in
/-- Blueprint `sk-lem-failure-field`: A failure is detected on the generic fibre.

If the base-change property `BC(p, Λ, q')` holds universally for all `q' < q` while
`BC(p, Λ, q)` fails for some `q ≥ 1`, there is a counterexample over a field, that is, an
`AlgebraicGeometry.Etale.FieldFailure`. Blueprint `sbc-lem-bc-failure-field` only assumes that
`BC(p, Λ, q)` does not hold universally; that form is
`AlgebraicGeometry.Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty`.

After restricting to an affine open of `S` the base of the failing square is quasi-compact
and quasi-separated. The base-change map is injective there
(`AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`), so some geometric stalk of its target
contains an element `ξ` outside its image, and the minimal-counterexample lemma applied to the
survival of `ξ` produces the field. -/
@[stacks 0F07]
theorem Etale.nonempty_fieldFailure (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q')
    (hfail : ¬ Etale.BaseChangeProperty Λ p q) :
    Nonempty (Etale.FieldFailure Λ p q) := by
  obtain ⟨U, hU, hUfail⟩ := Etale.exists_isAffineOpen_not_baseChangeProperty hfail
  have : IsAffine U := hU
  have hpb : IsPullback (pullback.fst p U.ι) (pullback.snd p U.ι) p U.ι :=
    IsPullback.of_hasPullback _ _
  have hprev' : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ (pullback.snd p U.ι) q' :=
    fun q' hq' ↦ (hprev q' hq').of_isPullback hpb
  obtain ⟨T, Y, g, e, h, _, _, sq, F, hF⟩ : ∃ (T Y : Scheme.{u}) (g : T ⟶ U) (e : Y ⟶ T)
      (h : Y ⟶ pullback p U.ι) (_ : QuasiCompact g) (_ : QuasiSeparated g)
      (sq : IsPullback e h g (pullback.snd p U.ι))
      (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      ¬ IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
    by_contra! H
    exact hUfail fun g e h _ _ sq F ↦ H _ _ g e h ‹_› ‹_› sq F
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated g
  have hmono := Etale.mono_baseChangeHomologyMap Λ q hq
    (hprev' (q - 1) (by omega)).baseChangeProperty sq F
  obtain ⟨x, hx⟩ : ∃ x : ↥(pullback p U.ι),
      ¬ IsIso ((Scheme.uliftPointSmallEtale _ x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq q F)) := by
    by_contra! H
    exact hF (Scheme.isIso_of_isIso_sheafFiber_map _ H)
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ ∉ Set.range ((Scheme.uliftPointSmallEtale _ x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ sq q F)).hom := by
    by_contra! H
    refine hx ((ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, H⟩)
    -- instance search does not find `LocallySmall.{u + 1}` for the small étale site
    have : LocallySmall.{u + 1} (pullback p U.ι).Etale := locallySmall_max.{u + 1, u}
    have : PreservesFiniteLimits
        ((Scheme.uliftPointSmallEtale _ x).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
      inferInstance
    exact (ModuleCat.mono_iff_injective _).1 (Functor.map_mono _ _)
  obtain ⟨K, _, φ, hφ⟩ := exists_spec_field_of_isQcqsLocalProperty T _
    (Etale.isQcqsLocalProperty_survivesBaseChange q hq hprev' sq F x ξ)
    (Etale.survivesBaseChange_id q sq F x ξ hξ)
  refine ⟨Etale.FieldFailure.mk (S' := U) (a := U.ι) (X' := pullback p U.ι)
    (p' := pullback.snd p U.ι) (b := pullback.fst p U.ι) (isPullback := hpb) (K := K)
    (g := φ ≫ g) (Y' := pullback (φ ≫ g) (pullback.snd p U.ι)) (e := pullback.fst _ _)
    (h := pullback.snd _ _) (isPullback_fibre := IsPullback.of_hasPullback _ _)
    (F := ((φ)^*[ModuleCat.{u + 1} Λ]).obj F) (not_isIso := fun hiso ↦ hφ ?_)⟩
  exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2 _

variable (p) in
/-- Blueprint `sbc-lem-bc-failure-field`: A failure of base change is detected over a field.

If the base-change property `BC(p, Λ, q')` holds universally for all `q' < q` while
`BC(p, Λ, q)` fails after some base change for some `q ≥ 1`, there is a counterexample over
a field. Apply `AlgebraicGeometry.Etale.nonempty_fieldFailure` to a failing base change of
`p` and paste the squares. -/
@[stacks 0F07]
theorem Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q')
    (hfail : ¬ Etale.UniversalBaseChangeProperty Λ p q) :
    Nonempty (Etale.FieldFailure Λ p q) := by
  simp only [Etale.UniversalBaseChangeProperty, not_forall] at hfail
  obtain ⟨S'', X'', a, b, p'', hpb, hfail⟩ := hfail
  obtain ⟨F⟩ := Etale.nonempty_fieldFailure Λ p'' q hq
    (fun q' hq' ↦ (hprev q' hq').of_isPullback hpb) hfail
  have := F.isAffine
  have := F.field
  exact ⟨{ F with a := F.a ≫ a, b := F.b ≫ b, isPullback := F.isPullback.paste_horiz hpb }⟩

end AlgebraicGeometry
