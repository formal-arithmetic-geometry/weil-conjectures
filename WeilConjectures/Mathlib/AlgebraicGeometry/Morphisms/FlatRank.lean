/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# The rank of a finite flat morphism as the rank of a sheaf of modules

`AlgebraicGeometry.Scheme.Hom.finrank f y` is the rank of a morphism `f : X ⟶ Y` at a point
`y : Y`, defined affine-locally in terms of the ring maps of `f`. This file computes it on an
affine open `U ∋ y`, as the rank of the `Γ(Y, U)`-algebra `Γ(X, f ⁻¹ᵁ U)` at the prime of `y`,
and matches the rank at a stalk of a quasi-coherent sheaf of modules with the rank at a stalk of
its module of sections over an affine open. Together these express `finrank f y` as the rank of
`f_* 𝒪_X` over `𝒪_Y` at `y`, which is the TODO recorded in
`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.flat_app`: the ring map of a flat affine morphism over an affine
  open is flat.
* `AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_app`: the rank of a finite flat morphism at a
  point `y` of an affine open `U` is the rank `(f.app U).hom.finrank` of the ring map of `f` over
  `U` at the prime ideal corresponding to `y`.
* `AlgebraicGeometry.Scheme.Modules.finrank_stalk_eq_rankAtStalk`: for a quasi-coherent sheaf `F`
  and a point `x` of an affine open `U`, the dimension of the stalk `F_x` over `𝒪_{X, x}` is the
  rank of the `Γ(X, U)`-module `Γ(F, U)` at the prime ideal of `x`.
* `AlgebraicGeometry.Scheme.Modules.genericRank_eq_rankAtStalk`: on an integral scheme, the
  generic rank of a quasi-coherent sheaf is the rank of its module of sections over any affine
  open containing the generic point, at the prime ideal of that point.

## Implementation notes

The stalk of a quasi-coherent sheaf at a point of an affine open is a localization of its
sections over that open (`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_germₗ`), hence a
base change along the localization `Γ(X, U) ⟶ 𝒪_{X, x}` of the structure sheaf; the rank at a
stalk is invariant under base change (`Module.rankAtStalk_isBaseChange`). At the generic point of
an integral scheme the local ring is the function field, so the stalk is free over it and its
rank at a stalk is its dimension.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-- **The ring map of a flat affine morphism over an affine open is flat**, the affine-local
counterpart of `AlgebraicGeometry.IsFinite.finite_app` for flatness. -/
lemma Scheme.Hom.flat_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] {U : Y.Opens}
    (hU : IsAffineOpen U) : (f.app U).hom.Flat := by
  rw [Scheme.Hom.app_eq_appLE]
  exact HasRingHomProperty.appLE @Flat f ‹_› ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hU.preimage f⟩ le_rfl

/-- **The rank of a finite flat morphism at a point of an affine open** `U` is the rank of the
ring map `f.app U` at the prime ideal corresponding to that point: on `U` the morphism `f` is the
spectrum of `f.app U`, and the rank of a morphism of affine schemes is the rank of the
corresponding ring map. -/
lemma Scheme.Hom.finrank_eq_finrank_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    {U : Y.Opens} (hU : IsAffineOpen U) (y : U) :
    f.finrank y.1 = (f.app U).hom.finrank (hU.primeIdealOf y) := by
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hfin : (f.app U).hom.Finite := f.finite_app U hU
  have hflat : (f.app U).hom.Flat := f.flat_app hU
  have : IsFinite (Spec.map (f.app U)) := (IsFinite.SpecMap_iff _).mpr hfin
  have : Flat (Spec.map (f.app U)) := Flat.SpecMap_iff.mpr hflat
  have hiso1 : IsIso U.toSpecΓ := by rw [← hU.isoSpec_hom]; infer_instance
  have hiso2 : IsIso (f ⁻¹ᵁ U).toSpecΓ := by rw [← hV.isoSpec_hom]; infer_instance
  have h1 : (f ∣_ U).finrank y = f.finrank y.1 :=
    Scheme.Hom.finrank_of_isPullback _ _ f U.ι (isPullback_morphismRestrict f U).flip y
  have h2 : (f ∣_ U).finrank y = (Spec.map (f.app U)).finrank (U.toSpecΓ y) :=
    Scheme.Hom.finrank_of_isPullback ((f ⁻¹ᵁ U).toSpecΓ) (f ∣_ U) (Spec.map (f.app U)) U.toSpecΓ
      (IsPullback.of_horiz_isIso ⟨Scheme.Opens.toSpecΓ_naturality f U⟩) y
  rw [← h1, h2, Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat, IsAffineOpen.primeIdealOf,
    ← hU.isoSpec_hom]

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- **The dimension of the stalk of a quasi-coherent sheaf at a point of an affine open is the
rank of its sections over that open at the corresponding prime ideal.** The stalk is the
localization of the sections at that prime, hence their base change along the localization of
`Γ(X, U)`, and the rank at a stalk is invariant under base change. -/
lemma finrank_stalk_eq_rankAtStalk (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) [Module.Finite Γ(X, U) Γ(F, U)] [Module.Flat Γ(X, U) Γ(F, U)]
    [Module.Free (X.presheaf.stalk x.1) (F.presheaf.stalk x.1)] :
    Module.finrank (X.presheaf.stalk x.1) (F.presheaf.stalk x.1)
      = Module.rankAtStalk (R := Γ(X, U)) Γ(F, U) (hU.primeIdealOf x) := by
  have : IsLocalization.AtPrime (X.presheaf.stalk x.1) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  have hloc := isLocalizedModule_germₗ F hU x
  have hbc : IsBaseChange (X.presheaf.stalk x.1) (germₗ F x) :=
    IsLocalizedModule.isBaseChange (hU.primeIdealOf x).asIdeal.primeCompl _ _
  let q : PrimeSpectrum (X.presheaf.stalk x.1) := ⟨IsLocalRing.maximalIdeal _, inferInstance⟩
  have hq : PrimeSpectrum.comap (algebraMap Γ(X, U) (X.presheaf.stalk x.1)) q
      = hU.primeIdealOf x :=
    PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal _ (hU.primeIdealOf x).asIdeal)
  calc Module.finrank (X.presheaf.stalk x.1) (F.presheaf.stalk x.1)
      = Module.rankAtStalk (R := X.presheaf.stalk x.1) (F.presheaf.stalk x.1) q :=
        (congrFun Module.rankAtStalk_eq_finrank_of_free q).symm
    _ = Module.rankAtStalk (R := Γ(X, U)) Γ(F, U)
          (PrimeSpectrum.comap (algebraMap Γ(X, U) (X.presheaf.stalk x.1)) q) :=
        Module.rankAtStalk_isBaseChange hbc q
    _ = _ := by rw [hq]

/-- **The generic rank of a quasi-coherent sheaf on an integral scheme is the rank of its
sections over an affine open containing the generic point**, at the prime ideal of that point.
The stalk at the generic point is a vector space over the function field, hence free, so its
dimension is its rank at a stalk. -/
lemma genericRank_eq_rankAtStalk [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (hx : genericPoint X ∈ U)
    [Module.Finite Γ(X, U) Γ(F, U)] [Module.Flat Γ(X, U) Γ(F, U)] :
    genericRank F
      = Module.rankAtStalk (R := Γ(X, U)) Γ(F, U) (hU.primeIdealOf ⟨genericPoint X, hx⟩) :=
  finrank_stalk_eq_rankAtStalk F hU ⟨genericPoint X, hx⟩

end Scheme.Modules

end AlgebraicGeometry
