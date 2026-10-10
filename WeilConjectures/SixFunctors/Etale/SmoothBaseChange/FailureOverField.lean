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

section TransitionComposition

/-- The associativity law for the composition isomorphisms
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the derived pullbacks, at an object, with
all three composites of the morphisms named. It is checked on the image of the homotopy
category, where it is the underived law `AlgebraicGeometry.Etale.upperStarComp_assoc'`. -/
lemma Etale.upperStarCompDerivedPlus_assoc {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g)
    (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f gh fgh
        (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K ≫
      D+((f)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) g h gh hgh).hom.app K) =
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) fg h fgh hfgh).hom.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f g fg hfg).hom.app
        (D+((h)^*[ModuleCat.{u + 1} Λ]).obj K) := sorry
/-- The transition maps `AlgebraicGeometry.Etale.lowerStarPlusTransition` are natural in the
complex. -/
lemma Etale.lowerStarPlusTransition_naturality {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    (h : Y ⟶ X) (h' : Y' ⟶ X) (w : a ≫ h = h')
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ K') :
    R+((h)_*[ModuleCat.{u + 1} Λ]).map f ≫ Etale.lowerStarPlusTransition Λ a h h' w K' =
      Etale.lowerStarPlusTransition Λ a h h' w K ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map (D+((a)^*[ModuleCat.{u + 1} Λ]).map f) := by
  have sq : CommSq a h' h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' w sq,
    Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' w sq]
  have hn := (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.naturality
    (R+((h)_*[ModuleCat.{u + 1} Λ]).map f)
  have hb := (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).naturality f
  simp only [Functor.id_map, Functor.comp_map] at hn hb
  rw [reassoc_of% hn, hb, Category.assoc]

/-- The transition maps `AlgebraicGeometry.Etale.lowerStarPlusTransition` compose: along
`a₁ : Y₁ ⟶ Y₂` and `a₂ : Y₂ ⟶ Y`, the composite of the two transition maps, followed by the
composition isomorphism of the pullbacks, is the transition map along `a₁ ≫ a₂`. Both sides are
derived base-change maps of degenerate squares, which paste horizontally. -/
lemma Etale.lowerStarPlusTransition_comp {X Y Y₂ Y₁ : Scheme.{u}} (a₂ : Y₂ ⟶ Y)
    (a₁ : Y₁ ⟶ Y₂) (a : Y₁ ⟶ Y) (ha : a₁ ≫ a₂ = a) (h : Y ⟶ X) (h₂ : Y₂ ⟶ X) (h₁ : Y₁ ⟶ X)
    (w₂ : a₂ ≫ h = h₂) (w₁ : a₁ ≫ h₂ = h₁) (w : a ≫ h = h₁)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.lowerStarPlusTransition Λ a₂ h h₂ w₂ K ≫
        Etale.lowerStarPlusTransition Λ a₁ h₂ h₁ w₁ (D+((a₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).inv.app K) =
      Etale.lowerStarPlusTransition Λ a h h₁ w K := by
  have sq₂ : CommSq a₂ h₂ h (𝟙 X) := ⟨by rw [w₂, Category.comp_id]⟩
  have sq₁ : CommSq a₁ h₁ h₂ (𝟙 X) := ⟨by rw [w₁, Category.comp_id]⟩
  have sq : CommSq a h₁ h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a₂ h h₂ w₂ sq₂,
    Etale.lowerStarPlusTransition_eq_baseChange Λ a₁ h₂ h₁ w₁ sq₁,
    Etale.lowerStarPlusTransition_eq_baseChange Λ a h h₁ w sq,
    Etale.baseChange_app_paste_horiz_of_eq Λ sq₂ sq₁ sq ha (Category.comp_id _) K]
  have hn := (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.naturality
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₂).app K)
  have hn' := (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.naturality
    ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app
      (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))
  have hc := Etale.upperStarCompDerivedPlus_id_right_inv_app (ModuleCat.{u + 1} Λ) (𝟙 X)
    (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)
  have hC : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.comp_id _).symm).hom.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) =
      D+((𝟙 X)^*[ModuleCat.{u + 1} Λ]).map ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ)
        X).inv.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)) := by
    rw [← cancel_mono ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.comp_id _).symm).inv.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)),
      Iso.hom_inv_id_app, hc]
    rfl
  simp only [Functor.id_map, Functor.id_obj] at hn hn'
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hn', hC]
/-- The derived base-change map of the degenerate square with sides `a`, `h'`, `h` and `𝟙 X` is
an isomorphism when `a` is a universal homeomorphism. The square is the vertical pasting of the
square with sides `a`, `a`, `𝟙 Y` and `𝟙 Y`, whose pushforwards are exact (`a_*` is an
equivalence) and whose underived base-change map is an isomorphism, with an identity square. -/
lemma Etale.isIso_baseChange_app_of_isUniversalHomeomorphism {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    [IsUniversalHomeomorphism a] (h : Y ⟶ X) (h' : Y' ⟶ X) (sq : CommSq a h' h (𝟙 X))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) := by
  have key : ∀ (f₀ : Y ⟶ X) (hf : 𝟙 Y ≫ h = f₀) (sq : CommSq a h' f₀ (𝟙 X)),
      IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq) := by
    rintro _ rfl sq
    have sq₁ : CommSq a a (𝟙 Y) (𝟙 Y) := ⟨by simp⟩
    have sq₂ : CommSq (𝟙 Y) h h (𝟙 X) := ⟨by simp⟩
    have := Etale.isEquivalence_lowerStar (ModuleCat.{u + 1} Λ) a
    have := Etale.isEquivalence_lowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y)
    have : IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁) :=
      Etale.isIso_derivedBaseChangeMapPlus_of_isIso_baseChangeMap _ sq₁
    have : IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂) := by
      rw [Etale.derivedBaseChangeMapPlus_id]
      infer_instance
    exact Etale.isIso_derivedBaseChangeMapPlus_of_paste_vert _ sq₁ sq₂ sq
      (by simpa using sq.w.symm)
  have := key h (Category.id_comp h) sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  infer_instance

/-- The transition map `Rh_*(e^* K) ⟶ Rh'_*(e'^*(π^* K))` between the targets of the derived
base-change maps over `T` and over `T'`, for `π : T' ⟶ T` covered by `a : Y' ⟶ Y` over `X`: the
transition map `AlgebraicGeometry.Etale.lowerStarPlusTransition` along `a`, followed by the
identification `a^* e^* ≅ e'^* π^*` of the derived pullbacks. In degree `q`, at a sheaf placed in
degree `0`, it is `AlgebraicGeometry.Etale.baseChangeTargetTransition`. -/
noncomputable def Etale.targetTransitionPlus {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).obj (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ⟶
      R+((h')_*[ModuleCat.{u + 1} Λ]).obj
        (D+((e')^*[ModuleCat.{u + 1} Λ]).obj (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K)) :=
  Etale.lowerStarPlusTransition Λ a h h' wh _ ≫
    R+((h')_*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).hom.app K)

/-- The identification `a^* e^* ≅ e'^* π^*` of derived pullbacks along a commutative square,
written with the composition isomorphisms along the diagonal, is the one written with
`AlgebraicGeometry.Etale.upperStarPlusComp` and an `eqToHom`. -/
lemma Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app {Y' Y T T' : Scheme.{u}}
    (a : Y' ⟶ Y) (e : Y ⟶ T) (e' : Y' ⟶ T') (π : T' ⟶ T) (wa : a ≫ e = e' ≫ π)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).hom.app K =
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app K ≫ eqToHom (by rw [wa]) ≫
        (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app K := by
  rw [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans,
    Etale.upperStarCompDerivedPlus_eq_eqToIso_trans, eqToIso_refl, Iso.refl_trans,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]

/-- The transition map `AlgebraicGeometry.Etale.baseChangeTargetTransition` is the degree-`q`
homology of `AlgebraicGeometry.Etale.targetTransitionPlus` at the sheaf placed in degree `0`,
followed by the identification `π^*(F[0]) ≅ (π^* F)[0]`. -/
lemma Etale.baseChangeTargetTransition_eq {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) (q : ℤ) (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.baseChangeTargetTransition Λ e h q π a e' h' wa wh F =
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.targetTransitionPlus Λ e h π a e' h' wa wh _ ≫
          R+((h')_*[ModuleCat.{u + 1} Λ]).map (D+((e')^*[ModuleCat.{u + 1} Λ]).map
            ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))) := by
  rw [Etale.baseChangeTargetTransition, Etale.targetTransitionPlus,
    Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app]
  simp only [Functor.map_comp, Category.assoc]

/-- The coherence of the identifications of derived pullbacks entering the composition law
`AlgebraicGeometry.Etale.targetTransitionPlus_comp`, for two stacked commutative squares
`a₂ ≫ e = e₂ ≫ π₂` and `a₁ ≫ e₂ = e₁ ≫ π₁`. It follows from three instances of the
associativity law `AlgebraicGeometry.Etale.upperStarCompDerivedPlus_assoc`. -/
lemma Etale.upperStarCompDerivedPlus_coherence {T T₂ T₁ Y Y₂ Y₁ : Scheme.{u}} (e : Y ⟶ T)
    (e₂ : Y₂ ⟶ T₂) (e₁ : Y₁ ⟶ T₁) (π₂ : T₂ ⟶ T) (π₁ : T₁ ⟶ T₂) (π : T₁ ⟶ T)
    (a₂ : Y₂ ⟶ Y) (a₁ : Y₁ ⟶ Y₂) (a : Y₁ ⟶ Y) (ha : a₁ ≫ a₂ = a) (hπ : π₁ ≫ π₂ = π)
    (wa₂ : a₂ ≫ e = e₂ ≫ π₂) (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁) (wa : a ≫ e = e₁ ≫ π)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).hom.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).inv.app K ≫
          (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).hom.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ e₂ (a₁ ≫ e₂) rfl).inv.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π₁ (a₁ ≫ e₂) wa₁).hom.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₁ π₂ π hπ.symm).inv.app K) =
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π (a ≫ e) wa).hom.app K := by
  have A1 := Etale.upperStarCompDerivedPlus_assoc Λ a₁ a₂ e a (a₂ ≫ e) (a ≫ e) ha.symm rfl rfl K
  have A2 := Etale.upperStarCompDerivedPlus_assoc Λ a₁ e₂ π₂ (a₁ ≫ e₂) (a₂ ≫ e) (a ≫ e) rfl wa₂
    (by simp only [← ha, Category.assoc, wa₂]) K
  have A3 := Etale.upperStarCompDerivedPlus_assoc Λ e₁ π₁ π₂ (a₁ ≫ e₂) π (a ≫ e) wa₁ hπ.symm
    (by simp only [← ha, Category.assoc, wa₂]) K
  have A1' : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).hom.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).inv.app K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ (a₂ ≫ e) (a ≫ e)
        (by simp only [← ha, Category.assoc])).hom.app K := by
    rw [← cancel_mono (D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).hom.app K)),
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
    rw [Category.assoc, A1, Iso.inv_hom_id_app_assoc]
  have A2' : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ (a₂ ≫ e) (a ≫ e)
        (by simp only [← ha, Category.assoc])).hom.app K ≫
      D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).hom.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ e₂ (a₁ ≫ e₂) rfl).inv.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a₁ ≫ e₂) π₂ (a ≫ e)
        (by simp only [← ha, Category.assoc, wa₂])).hom.app K := by
    rw [reassoc_of% A2, Iso.hom_inv_id_app, Category.comp_id]
  have A3' : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a₁ ≫ e₂) π₂ (a ≫ e)
        (by simp only [← ha, Category.assoc, wa₂])).hom.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π₁ (a₁ ≫ e₂) wa₁).hom.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₁ π₂ π hπ.symm).inv.app K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π (a ≫ e) wa).hom.app K := by
    rw [← reassoc_of% A3, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [Functor.map_comp, Category.assoc, reassoc_of% A1', reassoc_of% A2', A3']

/-- **The transition maps of the targets compose.** The transition map from `T` to `T₂` followed
by the one from `T₂` to `T₁` is, modulo the composition isomorphism `π₁^* π₂^* ≅ π^*`, the
transition map from `T` to `T₁`. -/
lemma Etale.targetTransitionPlus_comp {X T T₂ T₁ Y Y₂ Y₁ : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X)
    (π₂ : T₂ ⟶ T) (a₂ : Y₂ ⟶ Y) (e₂ : Y₂ ⟶ T₂) (h₂ : Y₂ ⟶ X) (wa₂ : a₂ ≫ e = e₂ ≫ π₂)
    (wh₂ : a₂ ≫ h = h₂) (π₁ : T₁ ⟶ T₂) (a₁ : Y₁ ⟶ Y₂) (e₁ : Y₁ ⟶ T₁) (h₁ : Y₁ ⟶ X)
    (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁) (wh₁ : a₁ ≫ h₂ = h₁) (π : T₁ ⟶ T) (a : Y₁ ⟶ Y)
    (ha : a₁ ≫ a₂ = a) (hπ : π₁ ≫ π₂ = π) (wa : a ≫ e = e₁ ≫ π) (wh : a ≫ h = h₁)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.targetTransitionPlus Λ e h π₂ a₂ e₂ h₂ wa₂ wh₂ K ≫
        Etale.targetTransitionPlus Λ e₂ h₂ π₁ a₁ e₁ h₁ wa₁ wh₁
          (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map (D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₁ π₂ π hπ.symm).inv.app K)) =
      Etale.targetTransitionPlus Λ e h π a e₁ h₁ wa wh K := by
  have hc := Etale.lowerStarPlusTransition_comp Λ a₂ a₁ a ha h h₂ h₁ wh₂ wh₁ wh
    (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)
  have hc' : Etale.lowerStarPlusTransition Λ a₂ h h₂ wh₂ (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        Etale.lowerStarPlusTransition Λ a₁ h₂ h₁ wh₁
          (D+((a₂)^*[ModuleCat.{u + 1} Λ]).obj (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)) =
      Etale.lowerStarPlusTransition Λ a h h₁ wh (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).hom.app
            (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)) := by
    rw [← hc, Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  simp only [Etale.targetTransitionPlus, Category.assoc]
  rw [reassoc_of% (Etale.lowerStarPlusTransition_naturality Λ a₁ h₂ h₁ wh₁
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).hom.app K)),
    reassoc_of% hc',
    ← Etale.upperStarCompDerivedPlus_coherence Λ e e₂ e₁ π₂ π₁ π a₂ a₁ a ha hπ wa₂ wa₁ wa K]
  simp only [Functor.map_comp, Category.assoc]

/-- The form of `AlgebraicGeometry.Etale.baseChange_app_comp_lowerStarPlusTransition` with the
transition map `AlgebraicGeometry.Etale.targetTransitionPlus` and a base `g'` of the second square
which is only equal to `π ≫ g`. -/
lemma Etale.baseChange_app_comp_targetTransitionPlus {X S T Y T' Y' : Scheme.{u}} {p : X ⟶ S}
    {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} (sq : CommSq e h g p) (π : T' ⟶ T) {e' : Y' ⟶ T'}
    {h' : Y' ⟶ X} (g' : T' ⟶ S) (hg : π ≫ g = g') (sq' : CommSq e' h' g' p) (a : Y' ⟶ Y)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K ≫
        Etale.targetTransitionPlus Λ e h π a e' h' wa wh K =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.lowerStarPlusTransition Λ π g g' hg K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
          (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  subst hg
  rw [Etale.targetTransitionPlus, Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app]
  exact Etale.baseChange_app_comp_lowerStarPlusTransition Λ sq π sq' a wa wh K

/-- The transition map `AlgebraicGeometry.Etale.lowerStarPlusTransition` along a universal
homeomorphism is an isomorphism. -/
lemma Etale.isIso_lowerStarPlusTransition {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    [IsUniversalHomeomorphism a] (h : Y ⟶ X) (h' : Y' ⟶ X) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Etale.lowerStarPlusTransition Λ a h h' w K) := by
  have sq : CommSq a h' h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' w sq]
  have := Etale.isIso_baseChange_app_of_isUniversalHomeomorphism Λ a h h' sq K
  infer_instance

/-- The transition map `AlgebraicGeometry.Etale.targetTransitionPlus` along a universal
homeomorphism `a` is an isomorphism. -/
lemma Etale.isIso_targetTransitionPlus {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) (π : T' ⟶ T) (a : Y' ⟶ Y) [IsUniversalHomeomorphism a] (e' : Y' ⟶ T')
    (h' : Y' ⟶ X) (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Etale.targetTransitionPlus Λ e h π a e' h' wa wh K) := by
  have := Etale.isIso_lowerStarPlusTransition Λ a h h' wh (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)
  rw [Etale.targetTransitionPlus]
  infer_instance

omit [CommRing Λ] in
/-- In a commutative square of modules whose horizontal sides are isomorphisms, an element is
in the range of the left side if and only if its image is in the range of the right side. -/
private lemma mem_range_iff_of_comm {R : Type*} [Ring R] {A B C D : ModuleCat R}
    (f : A ⟶ B) (g : C ⟶ D) (s : A ⟶ C) (t : B ⟶ D) [IsIso s] [IsIso t] (w : f ≫ t = s ≫ g)
    (y : B) : y ∈ Set.range f.hom ↔ t.hom y ∈ Set.range g.hom := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨s.hom z, by rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← w,
      ModuleCat.hom_comp, LinearMap.comp_apply]⟩
  · rintro ⟨z, hz⟩
    refine ⟨(inv s).hom z, ((ConcreteCategory.isIso_iff_bijective t).1 inferInstance).1 ?_⟩
    change (f ≫ t).hom _ = _
    rw [w, ← hz, ModuleCat.hom_comp, LinearMap.comp_apply, ← LinearMap.comp_apply s.hom,
      ← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply]

/-- The degree-`q` base-change map is the degree-`q` homology of the derived base-change map at
the sheaf placed in degree `0`. -/
lemma Etale.baseChangeHomologyMap_eq_homologyFunctor_map {X S T Y : Scheme.{u}} {p : X ⟶ S}
    {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.baseChangeHomologyMap Λ sq q F = (DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  rw [Etale.baseChangeHomologyMap, Etale.baseChangeHomologyNatTrans_eq,
    whiskerLeft_whiskerRight_app']

omit [CommRing Λ] in
/-- The naturality of a natural transformation `β` along the inverse of an isomorphism
`E ⋙ G ≅ G' ⋙ E'`, stated for abstract functors so that its instances at the concrete derived
functors are checked syntactically. -/
@[reassoc]
private lemma natTrans_app_comp_map_map_iso_inv_app {𝒜 𝒜' ℬ ℬ' 𝒞 𝒞' 𝒟 : Type*} [Category* 𝒜]
    [Category* 𝒜'] [Category* ℬ] [Category* ℬ'] [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟]
    {E : 𝒜 ⥤ ℬ} {G : ℬ ⥤ ℬ'} {G' : 𝒜 ⥤ 𝒜'} {E' : 𝒜' ⥤ ℬ'} (s : E ⋙ G ≅ G' ⋙ E')
    {P₁ : ℬ' ⥤ 𝒞} {P₂ : 𝒞 ⥤ 𝒟} {Q₁ : ℬ' ⥤ 𝒞'} {Q₂ : 𝒞' ⥤ 𝒟} (β : P₁ ⋙ P₂ ⟶ Q₁ ⋙ Q₂)
    (F : 𝒜) :
    β.app (E'.obj (G'.obj F)) ≫ Q₂.map (Q₁.map (s.inv.app F)) =
      P₂.map (P₁.map (s.inv.app F)) ≫ β.app (G.obj (E.obj F)) :=
  (β.naturality (s.inv.app F)).symm

omit [CommRing Λ] in
/-- The naturality of a natural transformation `β` along the inverse of an isomorphism
`H ≅ G₁ ⋙ G₂`, stated for abstract functors. -/
@[reassoc]
private lemma natTrans_app_comp_map_map_comp_iso_inv_app {𝒜 ℬ ℬ' 𝒞 𝒞' 𝒟 : Type*} [Category* 𝒜]
    [Category* ℬ] [Category* ℬ'] [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟]
    {H : 𝒜 ⥤ ℬ'} {G₁ : 𝒜 ⥤ ℬ} {G₂ : ℬ ⥤ ℬ'} (s : H ≅ G₁ ⋙ G₂)
    {P₁ : ℬ' ⥤ 𝒞} {P₂ : 𝒞 ⥤ 𝒟} {Q₁ : ℬ' ⥤ 𝒞'} {Q₂ : 𝒞' ⥤ 𝒟} (β : P₁ ⋙ P₂ ⟶ Q₁ ⋙ Q₂)
    (F : 𝒜) :
    β.app (G₂.obj (G₁.obj F)) ≫ Q₂.map (Q₁.map (s.inv.app F)) =
      P₂.map (P₁.map (s.inv.app F)) ≫ β.app (H.obj F) :=
  (β.naturality (s.inv.app F)).symm

/-- The comparison underlying `AlgebraicGeometry.Etale.survivesBaseChange_comp_iff_of_surjective`,
for arbitrary Cartesian squares over `T₂` and over `T₁` and a universal homeomorphism
`i : T₁ ⟶ T₂` whose base change `a'` is a universal homeomorphism. The transitions from `T₂` to
`T₁` of the sources and of the targets of the base-change maps are isomorphisms, the transition
from `T` to `T₁` factors through the one to `T₂`, and the base-change maps commute with them, so
the image of `ξ` lies in the image of the base-change map over `T₁` if and only if it does over
`T₂`. -/
theorem Etale.mem_range_iff_of_isUniversalHomeomorphism {X S T Y T₂ Y₂ T₁ Y₁ : Scheme.{u}}
    {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    (f₂ : T₂ ⟶ T) {e₂ : Y₂ ⟶ T₂} {h₂ : Y₂ ⟶ X} (sq₂ : IsPullback e₂ h₂ (f₂ ≫ g) p)
    (a₂ : Y₂ ⟶ Y) (wa₂ : a₂ ≫ e = e₂ ≫ f₂) (wh₂ : a₂ ≫ h = h₂)
    (i : T₁ ⟶ T₂) [IsUniversalHomeomorphism i] {e₁ : Y₁ ⟶ T₁} {h₁ : Y₁ ⟶ X}
    (sq₁ : IsPullback e₁ h₁ ((i ≫ f₂) ≫ g) p) (a₁ : Y₁ ⟶ Y) (wa₁ : a₁ ≫ e = e₁ ≫ i ≫ f₂)
    (wh₁ : a₁ ≫ h = h₁) (a' : Y₁ ⟶ Y₂) [IsUniversalHomeomorphism a'] (wa' : a' ≫ e₂ = e₁ ≫ i)
    (wh' : a' ≫ h₂ = h₁) (ha : a' ≫ a₂ = a₁) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeTargetTransition Λ e h q (i ≫ f₂) a₁ e₁ h₁ wa₁ wh₁ F)).hom ξ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq₁ q (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F))).hom ↔
    ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeTargetTransition Λ e h q f₂ a₂ e₂ h₂ wa₂ wh₂ F)).hom ξ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq₂ q (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F))).hom := by
  obtain ⟨s, t, hs, ht, hst, htT⟩ : ∃ (s : (Etale.baseChangeSourceFunctor Λ p (f₂ ≫ g) q).obj
        (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ⟶ (Etale.baseChangeSourceFunctor Λ p
          ((i ≫ f₂) ≫ g) q).obj (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F))
      (t : (Etale.baseChangeTargetFunctor Λ e₂ h₂ q).obj (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ⟶
        (Etale.baseChangeTargetFunctor Λ e₁ h₁ q).obj (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F)),
      IsIso s ∧ IsIso t ∧
        Etale.baseChangeHomologyMap Λ sq₂ q (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ≫ t =
          s ≫ Etale.baseChangeHomologyMap Λ sq₁ q (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ∧
        Etale.baseChangeTargetTransition Λ e h q f₂ a₂ e₂ h₂ wa₂ wh₂ F ≫ t =
          Etale.baseChangeTargetTransition Λ e h q (i ≫ f₂) a₁ e₁ h₁ wa₁ wh₁ F := by
    refine ⟨(DerivedCategory.Plus.homologyFunctor _ q).map (D+((p)^*[ModuleCat.{u + 1} Λ]).map
        (R+((f₂ ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((((f₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F) ≫
        Etale.lowerStarPlusTransition Λ i (f₂ ≫ g) ((i ≫ f₂) ≫ g) (Category.assoc _ _ _).symm
          (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
        R+(((i ≫ f₂) ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) i f₂ (i ≫ f₂) rfl).inv.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
            ((((i ≫ f₂))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              F))),
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h₂)_*[ModuleCat.{u + 1} Λ]).map (D+((e₂)^*[ModuleCat.{u + 1} Λ]).map
          ((((f₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F)) ≫
        Etale.targetTransitionPlus Λ e₂ h₂ i a' e₁ h₁ wa' wh'
          (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map (D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) i f₂ (i ≫ f₂) rfl).inv.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
            ((((i ≫ f₂))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              F))), ?_, ?_, ?_, ?_⟩
    · have := Etale.isIso_lowerStarPlusTransition Λ i (f₂ ≫ g) ((i ≫ f₂) ≫ g)
        (Category.assoc _ _ _).symm
        (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
      infer_instance
    · have := Etale.isIso_targetTransitionPlus Λ e₂ h₂ i a' e₁ h₁ wa' wh'
        (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
      infer_instance
    · rw [Etale.baseChangeHomologyMap_eq_homologyFunctor_map,
        Etale.baseChangeHomologyMap_eq_homologyFunctor_map, ← Functor.map_comp, ← Functor.map_comp]
      congr 1
      have c := Etale.baseChange_app_comp_targetTransitionPlus Λ sq₂.toCommSq i ((i ≫ f₂) ≫ g)
        (Category.assoc _ _ _).symm sq₁.toCommSq a' wa' wh'
        (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
      rw [natTrans_app_comp_map_map_iso_inv_app_assoc, reassoc_of% c]
      simp only [Functor.map_comp, Category.assoc]
      rw [natTrans_app_comp_map_map_comp_iso_inv_app_assoc, natTrans_app_comp_map_map_iso_hom_app]
    · rw [Etale.baseChangeTargetTransition_eq, Etale.baseChangeTargetTransition_eq,
        ← Functor.map_comp]
      congr 1
      have hT := Etale.targetTransitionPlus_comp Λ e h f₂ a₂ e₂ h₂ wa₂ wh₂ i a' e₁ h₁ wa' wh'
        (i ≫ f₂) a₁ ha rfl wa₁ wh₁ ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
      simp only [Category.assoc, Functor.map_comp] at hT ⊢
      rw [← Functor.map_comp_assoc (R+((h₂)_*[ModuleCat.{u + 1} Λ])),
        ← Functor.map_comp (D+((e₂)^*[ModuleCat.{u + 1} Λ])), Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rw [reassoc_of% hT]
  have := hs
  have := ht
  rw [← htT, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact (mem_range_iff_of_comm _ _ ((X.uliftPointSmallEtale x).sheafFiber.map s)
    ((X.uliftPointSmallEtale x).sheafFiber.map t)
    (by rw [← Functor.map_comp, ← Functor.map_comp, hst]) _).symm

end TransitionComposition

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
    Etale.SurvivesBaseChange Λ q sq F x ξ (i ≫ f₂) ↔ Etale.SurvivesBaseChange Λ q sq F x ξ f₂ := by
  have : Surjective i := ⟨hi⟩
  -- the fibre products over `T₂` and over `T₁`
  have sq₂ := IsPullback.of_hasPullback (f₂ ≫ g) p
  have sq₁ := IsPullback.of_hasPullback ((i ≫ f₂) ≫ g) p
  obtain ⟨a', hae, hah⟩ : ∃ a' : pullback ((i ≫ f₂) ≫ g) p ⟶ pullback (f₂ ≫ g) p,
      a' ≫ pullback.fst (f₂ ≫ g) p = pullback.fst ((i ≫ f₂) ≫ g) p ≫ i ∧
        a' ≫ pullback.snd (f₂ ≫ g) p = pullback.snd ((i ≫ f₂) ≫ g) p :=
    ⟨pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
      ((Category.assoc _ _ _).trans (by rw [← Category.assoc i f₂ g]; exact pullback.condition)),
      by simp, by simp⟩
  have hpb : IsPullback (pullback.fst ((i ≫ f₂) ≫ g) p) a' i (pullback.fst (f₂ ≫ g) p) := by
    refine IsPullback.of_bot ?_ hae.symm sq₂
    rw [hah, ← Category.assoc]
    exact sq₁
  have : IsUniversalHomeomorphism a' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb inferInstance
  have ha : a' ≫ sq.lift (pullback.fst (f₂ ≫ g) p ≫ f₂) (pullback.snd (f₂ ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition) =
      sq.lift (pullback.fst ((i ≫ f₂) ≫ g) p ≫ i ≫ f₂) (pullback.snd ((i ≫ f₂) ≫ g) p)
        ((Category.assoc _ _ _).trans pullback.condition) :=
    sq.hom_ext (by simp [reassoc_of% hae]) (by simp [hah])
  unfold Etale.SurvivesBaseChange
  exact not_congr (Etale.mem_range_iff_of_isUniversalHomeomorphism Λ q F x ξ f₂ sq₂ _
    (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) i sq₁ _ (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) a'
    hae hah ha)

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
