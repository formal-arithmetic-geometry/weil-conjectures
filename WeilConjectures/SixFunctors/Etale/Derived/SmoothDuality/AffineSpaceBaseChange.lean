/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunctionBaseChange

/-!
# Base change for the projections of projective lines and affine spaces over any base

For every scheme `S` on which the exponent of `Λ` is invertible (affine or not), the canonical
base change maps `Lg'^* Rp^! ⟶ Rp'^! Lg^*` of the projections `ℙ¹_S ⟶ S`, `𝔸¹_S ⟶ S` and
`𝔸^d_S ⟶ S` are isomorphisms, for every cartesian square with quasi-compact base change admitting
a compactification (the base change clause of blueprint `sk-lem-geo-affine-local`).

The projective-line case is the formal consequence of the compatibility of the projective-line
adjunction with base change
(`AlgebraicGeometry.Etale.projectiveLineAdjunctionBaseChange_of_isNormalized`, blueprint
`det-sp-p1-adjunction`), applied to the normalized Tate twist `μ_n ⊗ Λ`
(`AlgebraicGeometry.Etale.hasKummerClass`): the base change map does not depend on a twist. The
affine line is the standard chart of `ℙ¹_S`, and affine spaces are iterated affine lines. These
are the arguments of `AlgebraicGeometry.Etale.projectiveLineBaseChange_of_adjunction`,
`AlgebraicGeometry.Etale.affineLineBaseChange_of_projectiveLineBaseChange` and
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_affineSpace`, which are
stated over affine bases.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_projectiveLine`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_affineLine`
- `isIso_rightDerivedUpperShriekBaseChangeMap_affineSpace_of_hasInvertibleExponent`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Base change for the projective line over any base.** For every scheme `S` on which the
exponent of `Λ` is invertible and every cartesian square of `q : ℙ¹_S ⟶ S` with quasi-compact
base change admitting a compactification, the base change map `Lg'^* Rq^! ⟶ Rq'^! Lg^*` is an
isomorphism: it is the mate of the inverse of `Ex_!`, computed through the projective-line
adjunctions of the normalized twist `μ_n ⊗ Λ`, whose counits commute with base change. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_projectiveLine ⦃S : Scheme.{u}⦄
    [HasInvertibleExponent Λ S] ⦃S' P' : Scheme.{u}⦄ {g : S' ⟶ S} {q' : P' ⟶ S'}
    {g' : P' ⟶ ℙ(Option (ULift.{u} (Fin 1)); S)}
    (sq : IsPullback g' q' (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) g) [HasCompactification q']
    [QuasiCompact q'] : IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have : NeZero (ringChar Λ) := ⟨CharP.char_ne_zero_of_finite Λ (ringChar Λ)⟩
  let : HasTateTwist Λ := (hasKummerClass Λ).toHasTateTwist
  have : HasTateTwist.IsNormalized Λ := ⟨⟨hasKummerClass Λ, rfl, hasKummerClass_isNormalized Λ⟩⟩
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom (_ ↘ S)
  have : HasInvertibleExponent Λ P' := .of_hom (g' ≫ _ ↘ S)
  have : HasInvertibleExponent Λ S' := .of_hom g
  obtain ⟨adj, adj', hc⟩ := projectiveLineAdjunctionBaseChange_of_isNormalized Λ sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact isIso_mateEquiv_app_of_counit (rightDerivedUpperShriekAdjunction _ _)
    (rightDerivedUpperShriekAdjunction _ _) adj adj'
    (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)) K
    ((leftDerivedUpperStarTwistShiftIso Λ g' 1 _).hom ≫
      (twistShift Λ P' 1).map ((derivedSquareUpperStarIso _ sq.toCommSq).inv.app K))
    (by simp [← hc K])

/-- **Base change for the affine line over any base.** The projection `𝔸¹_S ⟶ S` is the
standard chart `𝔸¹_S ⟶ ℙ¹_S`, a quasi-compact open immersion, followed by `ℙ¹_S ⟶ S`; base
change maps compose, and base change holds for open immersions and for the projective line
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_projectiveLine`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_affineLine ⦃S : Scheme.{u}⦄
    [HasInvertibleExponent Λ S] ⦃S' P' : Scheme.{u}⦄ {g : S' ⟶ S} {p' : P' ⟶ S'}
    {g' : P' ⟶ 𝔸(ULift.{u} (Fin 1); S)} (sq : IsPullback g' p' (𝔸(ULift.{u} (Fin 1); S) ↘ S) g)
    [HasCompactification p'] [QuasiCompact p'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have : QuasiCompact (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S ≫
      ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) := by
    rw [AffineSpace.toRelativeProjectiveSpace_over]
    infer_instance
  have : QuasiCompact (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S) :=
    .of_comp _ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
  have : HasCompactification (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  exact isIso_rightDerivedUpperShriekBaseChangeMap_of_comp
    (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)
    (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) (AffineSpace.toRelativeProjectiveSpace_over _ S) sq
    (fun _ _ _ _ _ sq' _ _ ↦
      isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sq')
    (fun _ _ _ _ _ sq' _ _ ↦ isIso_rightDerivedUpperShriekBaseChangeMap_projectiveLine Λ sq')

/-- **Base change for affine spaces over any base.** For every scheme `S` on which the exponent
of `Λ` is invertible, the base change maps of the projection `p_d : 𝔸^d_S ⟶ S` are
isomorphisms. For `d = 0` the projection is an isomorphism; for `d + 1` it is, through
`𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`, the composite of the affine-line projection over `𝔸^d_S` and of
`p_d`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_affineSpace_of_hasInvertibleExponent (d : ℕ)
    (S : Scheme.{u}) [HasInvertibleExponent Λ S] ⦃S' P' : Scheme.{u}⦄
    {g : S' ⟶ S} {p' : P' ⟶ S'} {g' : P' ⟶ 𝔸(ULift.{u} (Fin d); S)}
    (sq : IsPullback g' p' (𝔸(ULift.{u} (Fin d); S) ↘ S) g) [HasCompactification p']
    [QuasiCompact p'] : IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  induction d generalizing S' P' with
  | zero => exact isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sq
  | succ d ih =>
    set φ : 𝔸(ULift.{u} (Fin (d + 1)); S) ≅ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) :=
      AffineSpace.reindexIso S ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
        (finSumFinEquiv.trans Equiv.ulift.symm)) ≪≫ AffineSpace.sumIso S
    set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) ↘ 𝔸(ULift.{u} (Fin d); S)
    set p := 𝔸(ULift.{u} (Fin d); S) ↘ S
    have : HasCompactification (φ.hom ≫ q) := HasCompactification.comp_of_isOpenImmersion q φ.hom
    have h : (φ.hom ≫ q) ≫ p = 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S := by
      rw [Category.assoc, Iso.trans_hom, Category.assoc, AffineSpace.sumIso_hom_over_over,
        AffineSpace.reindexIso_hom, AffineSpace.reindex_over]
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin d); S) := .of_hom p
    refine isIso_rightDerivedUpperShriekBaseChangeMap_of_comp (φ.hom ≫ q) p h sq
      (fun _ _ _ _ _ sq' _ _ ↦ ?_) (fun _ _ _ _ _ sq' _ _ ↦ ih sq')
    exact isIso_rightDerivedUpperShriekBaseChangeMap_of_comp φ.hom q rfl sq'
      (fun _ _ _ _ _ sq'' _ _ ↦
        isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sq'')
      (fun _ _ _ _ _ sq'' _ _ ↦ isIso_rightDerivedUpperShriekBaseChangeMap_affineLine Λ sq'')

end Etale

end AlgebraicGeometry
