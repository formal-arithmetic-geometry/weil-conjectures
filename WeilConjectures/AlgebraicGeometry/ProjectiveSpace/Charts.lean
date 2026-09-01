/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The standard affine charts of projective space

The standard open `D₊(Tᵢ)` of `ℙ(n; S)` is the affine space `𝔸({j : n // j ≠ i}; S)` over `S`,
with the affine coordinates given by the quotients `Tⱼ / Tᵢ`.

Over the integral model, this is `AlgebraicGeometry.Proj.basicOpenIsoSpec` combined with
`MvPolynomial.homogeneousLocalizationAwayXEquiv`, which identifies the degree-zero part of
`ℤ[T]_{Tᵢ}` with the polynomial ring `ℤ[Yⱼ : j ≠ i]`. Since `ℙ(n; S)` and `𝔸(m; S)` are both
defined as base changes of their integral models along `S ⟶ Spec ℤ`, and `D₊(Tᵢ) ⊆ ℙ(n; S)`
is the preimage of `D₊(Tᵢ) ⊆ ℙⁿ_ℤ`, the chart over `S` is obtained by base change.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.standardOpenIso` — the isomorphism of `S`-schemes
  `D₊(Tᵢ) ≅ 𝔸({j : n // j ≠ i}; S)`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.standardOpenIso_hom_over` — the chart isomorphism is a
  morphism over `S`.
- `AlgebraicGeometry.ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom` — the
  computation rule: for `g : X ⟶ S` and sections `s : n → Γ(X, ⊤)` generating the unit ideal,
  the morphism `X_{s i} ⟶ 𝔸({j // j ≠ i}; S)` obtained by restricting `homOfSections g s hs`
  and applying the chart isomorphism is `AffineSpace.homOfVector` for the vector of
  quotients `s j / s i`.

## Implementation notes

`MvPolynomial.homogeneousLocalizationAwayXEquiv` takes a `DecidableEq` instance on the index
type, which the chart isomorphism should not carry around. Since everything here is
noncomputable anyway, `Classical.decEq` is enabled as a local instance, so that a single
instance is used throughout the file and none appears in any statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra Classical.decEq

variable (n : Type u) (S : Scheme.{u}) (i : n)

/-- Over the integral model, the standard open `D₊(Tᵢ)` of `ℙⁿ_ℤ` is the spectrum of the
polynomial ring `ℤ[Yⱼ : j ≠ i]`, the variable `Yⱼ` corresponding to the quotient `Tⱼ / Tᵢ`. -/
def projIntBasicOpenIso :
    (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial {j : n // j ≠ i} (ULift.{u} ℤ))) :=
  Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one _ i) one_pos ≪≫
    Scheme.Spec.mapIso
      (homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) i).symm.toRingEquiv.toCommRingCatIso.op

@[simp]
lemma projIntBasicOpenIso_hom :
    (projIntBasicOpenIso n i).hom =
      (Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one _ i) one_pos).hom ≫
        Spec.map (CommRingCat.ofHom
          (homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) i).symm.toRingHom) :=
  rfl

/-- `ℙ(n; S)` is the base change of the integral model `ℙⁿ_ℤ` along `S ⟶ Spec ℤ`. -/
lemma isPullback_toProjInt :
    IsPullback (toProjInt n S) (ℙ(n; S) ↘ S)
      (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ))) (terminal.from S) :=
  (IsPullback.of_hasPullback _ _).flip

/-- The standard open `D₊(Tᵢ)` of `ℙ(n; S)` is the base change of the standard open `D₊(Tᵢ)`
of the integral model `ℙⁿ_ℤ`. -/
lemma isPullback_standardOpen :
    IsPullback ((toProjInt n S).resLE _ (standardOpen n S i) le_rfl)
      ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
      (terminal.from _) (terminal.from S) := by
  have h := (isPullback_morphismRestrict (toProjInt n S)
    (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i))).paste_vert
      (isPullback_toProjInt n S)
  have hr : (toProjInt n S).resLE
      (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i))
        (standardOpen n S i) le_rfl =
      toProjInt n S ∣_ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i) :=
    Scheme.Hom.resLE_eq_morphismRestrict ..
  exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id]; exact hr.symm.trans (Category.id_comp _).symm)
    (by rw [Iso.refl_hom, Category.comp_id]; exact (Category.id_comp _).symm)
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- The variant of `isPullback_standardOpen` where the integral chart is read as the affine
space `Spec ℤ[Yⱼ : j ≠ i]`. -/
lemma isPullback_standardOpen_projIntBasicOpenIso :
    IsPullback ((toProjInt n S).resLE _ (standardOpen n S i) le_rfl ≫
        (projIntBasicOpenIso n i).hom)
      ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
      (terminal.from (Spec (CommRingCat.of (MvPolynomial {j : n // j ≠ i} (ULift.{u} ℤ)))))
      (terminal.from S) :=
  (isPullback_standardOpen n S i).of_iso (Iso.refl _) (projIntBasicOpenIso n i) (Iso.refl _)
    (Iso.refl _) (by simp) (by simp) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- `𝔸(m; S)` is the base change of the integral model `Spec ℤ[Y]` along `S ⟶ Spec ℤ`. -/
lemma isPullback_toSpecMvPoly (m : Type u) :
    IsPullback (AffineSpace.toSpecMvPoly m S) (𝔸(m; S) ↘ S)
      (terminal.from (Spec (CommRingCat.of (MvPolynomial m (ULift.{u} ℤ))))) (terminal.from S) :=
  (IsPullback.of_hasPullback _ _).flip

/-- **The standard affine charts of projective space**: the standard open `D₊(Tᵢ)` of
`ℙ(n; S)`, where the `i`-th homogeneous coordinate does not vanish, is the affine space
`𝔸({j : n // j ≠ i}; S)` over `S`, with affine coordinates `Tⱼ / Tᵢ`. -/
def standardOpenIso : (standardOpen n S i).toScheme ≅ 𝔸({j : n // j ≠ i}; S) :=
  (isPullback_standardOpen_projIntBasicOpenIso n S i).isoIsPullback _ _
    (isPullback_toSpecMvPoly S _)

/-- The chart isomorphism is an isomorphism of `S`-schemes. -/
@[reassoc (attr := simp)]
lemma standardOpenIso_hom_over :
    (standardOpenIso n S i).hom ≫ 𝔸({j : n // j ≠ i}; S) ↘ S =
      (standardOpen n S i).ι ≫ ℙ(n; S) ↘ S :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc (attr := simp)]
lemma standardOpenIso_inv_ι_over :
    (standardOpenIso n S i).inv ≫ (standardOpen n S i).ι ≫ ℙ(n; S) ↘ S =
      𝔸({j : n // j ≠ i}; S) ↘ S :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

/-- The chart isomorphism is compatible with the charts of the integral model. -/
@[reassoc (attr := simp)]
lemma standardOpenIso_hom_toSpecMvPoly :
    (standardOpenIso n S i).hom ≫ AffineSpace.toSpecMvPoly {j : n // j ≠ i} S =
      (toProjInt n S).resLE _ (standardOpen n S i) le_rfl ≫ (projIntBasicOpenIso n i).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

section Sections

variable {X : Scheme.{u}} (g : X ⟶ S) (s : n → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)

variable {n S} in
/-- Evaluating the homogeneous coordinates at the sections `s` maps powers of `Tᵢ` to powers
of `s i`. -/
lemma powers_X_le_comap_powers (i : n) :
    Submonoid.powers (MvPolynomial.X i : MvPolynomial n (ULift.{u} ℤ)) ≤
      Submonoid.comap (evalSections s) (Submonoid.powers (s i)) := by
  rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
  simp

variable {n S} in
/-- The ring map `ℤ[Yⱼ : j ≠ i] ⟶ Γ(X, ⊤)_{s i}` sending the variable `Yⱼ` to the quotient
`s j / s i`: the degree-zero part of `evalSections s` localized away from `Tᵢ`. This is the map
on coordinate rings underlying the computation rule below. -/
def evalSectionsAway (i : n) :
    CommRingCat.of (MvPolynomial {j : n // j ≠ i} (ULift.{u} ℤ)) ⟶
      CommRingCat.of (Localization.Away (s i)) :=
  CommRingCat.ofHom (homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) i).symm.toRingHom ≫
    CommRingCat.ofHom
      ((IsLocalization.map _ (evalSections s) (powers_X_le_comap_powers s i)).comp
        (algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule n (ULift.{u} ℤ))
          (MvPolynomial.X i))
          (Localization.Away (MvPolynomial.X i : MvPolynomial n (ULift.{u} ℤ)))))

variable {n S} in
@[simp]
lemma evalSectionsAway_X (i : n) (j : {j : n // j ≠ i}) :
    evalSectionsAway s i (MvPolynomial.X j) =
      IsLocalization.mk' (Localization.Away (s i)) (s j.1)
        (⟨s i, Submonoid.mem_powers _⟩ : Submonoid.powers (s i)) := by
  rw [evalSectionsAway, CommRingCat.comp_apply]
  change ((IsLocalization.map (Localization.Away (s i)) (evalSections s)
      (powers_X_le_comap_powers s i)).comp (algebraMap _ _))
      ((homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) i).symm (MvPolynomial.X j)) = _
  rw [homogeneousLocalizationAwayXEquiv_symm_X, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  · exact evalSections_X s j.1
  · exact Subtype.ext (by simp)

set_option backward.isDefEq.respectTransparency.types false in
variable {n S} in
/-- Read through the chart isomorphism, the morphism `X_{s i} ⟶ 𝔸({j // j ≠ i}; S)` induced
by `homOfSections g s hs` is `Spec` of the map `Yⱼ ↦ s j / s i` on coordinate rings. -/
lemma homOfSections_resLE_standardOpenIso_hom_toSpecMvPoly (i : n) :
    ((homOfSections g s hs).resLE (standardOpen n S i) (X.basicOpen (s i))
        (homOfSections_preimage_standardOpen g s hs i).ge ≫ (standardOpenIso n S i).hom) ≫
      AffineSpace.toSpecMvPoly {j : n // j ≠ i} S =
      X.toSpecAway (s i) ≫ Spec.map (evalSectionsAway s i) := by
  rw [evalSectionsAway, Spec.map_comp, Category.assoc, standardOpenIso_hom_toSpecMvPoly,
    reassoc_of% homOfSections_resLE_comp_toProjInt_resLE g s hs i, projIntBasicOpenIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t ↦ t ≫ Spec.map (CommRingCat.ofHom
        (homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) i).symm.toRingHom))
      (Proj.toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom
        (homogeneousSubmodule n (ULift.{u} ℤ)) (evalSections s) (evalSections_X s i) _ _)).trans
      (Category.assoc _ _ _))

variable {n S} in
/-- **The computation rule for the standard charts**: for a morphism `g : X ⟶ S` and a family
`s : n → Γ(X, ⊤)` of global sections generating the unit ideal, the morphism
`X_{s i} ⟶ 𝔸({j // j ≠ i}; S)` obtained by restricting `homOfSections g s hs` to the standard
open `D₊(Tᵢ)` and applying the chart isomorphism is the morphism over `g` given by the family
of quotients `s j / s i`. -/
theorem homOfSections_resLE_standardOpenIso_hom (i : n) :
    (homOfSections g s hs).resLE (standardOpen n S i) (X.basicOpen (s i))
        (homOfSections_preimage_standardOpen g s hs i).ge ≫ (standardOpenIso n S i).hom =
      AffineSpace.homOfVector ((X.basicOpen (s i)).ι ≫ g)
        (fun j ↦ X.divBasicOpen (s j.1) (s i)) := by
  refine AffineSpace.hom_ext ?_ fun j ↦ ?_
  · rw [Category.assoc, standardOpenIso_hom_over, homOfSections_resLE_ι_over,
      AffineSpace.homOfVector_over]
  · rw [AffineSpace.homOfVector_appTop_coord,
      show AffineSpace.coord S j =
        AffineSpace.toSpecMvPolyIntEquiv _ (AffineSpace.toSpecMvPoly _ S) j from rfl,
      ← AffineSpace.toSpecMvPolyIntEquiv_comp,
      homOfSections_resLE_standardOpenIso_hom_toSpecMvPoly g s hs i,
      AffineSpace.toSpecMvPolyIntEquiv_comp_SpecMap, ← Scheme.awayToBasicOpen_apply,
      evalSectionsAway_X, Scheme.awayToBasicOpen_mk']

end Sections

end AlgebraicGeometry.ProjectiveSpace
