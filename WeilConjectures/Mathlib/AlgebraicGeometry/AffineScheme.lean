/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# `Spec` of a restriction map and the canonical isomorphisms of affine opens

We record that `Spec` of a restriction map between affine opens intertwines the canonical
isomorphisms `Spec Γ(X, U) ≅ U` with the inclusion of opens, that the algebra map
realizing `Γ(X, X.basicOpen f)` as a localization is the restriction map of the structure
sheaf.

We also compute the restriction of `X.toSpecΓ` over a basic open `D(r) ⊆ Spec Γ(X, ⊤)`:
it is `Spec` of the localization map `Γ(X, ⊤)[1/r] →+* Γ(X, X.basicOpen r)`, see
`AlgebraicGeometry.toSpecΓ_resLE_basicOpenIsoSpecAway`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The `Spec` of a restriction map intertwines the canonical isomorphisms
`Spec Γ(X, U) ≅ U` with the inclusion of opens. -/
lemma specMap_res_isoSpec_inv {U V : X.affineOpens} (hUV : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hUV).op) ≫ V.2.isoSpec.inv =
      U.2.isoSpec.inv ≫ X.homOfLE hUV := by
  rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι,
    V.2.map_fromSpec U.2 (homOfLE (X := X.Opens) hUV).op]

/-- The algebra map exhibiting the sections over a basic open as a localization is the
restriction map of the structure sheaf. -/
lemma algebraMap_basicOpen_eq {U : X.Opens} (f : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
  rfl

/-- Restricting the canonical morphism `X ⟶ Spec Γ(X, ⊤)` over the basic open `D(r)`
identifies the morphism `X.basicOpen r ⟶ Spec Γ(X, ⊤)[1/r]` with `Spec` of the canonical
localization map `Γ(X, ⊤)[1/r] →+* Γ(X, X.basicOpen r)`. -/
@[reassoc]
lemma toSpecΓ_resLE_basicOpenIsoSpecAway (r : Γ(X, ⊤)) :
    X.toSpecΓ.resLE (PrimeSpectrum.basicOpen r) (X.basicOpen r)
        (X.toSpecΓ_preimage_basicOpen r).ge ≫ (basicOpenIsoSpecAway r).hom =
      (X.basicOpen r).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.lift (S := Localization.Away r) r
          (Scheme.isUnit_algebraMap_basicOpen r))) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away r)))),
    Category.assoc, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap, Scheme.Hom.resLE_comp_ι,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]
  exact (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top _).symm
/-- Distinct points of an affine open have distinct associated primes. -/
lemma IsAffineOpen.primeIdealOf_injective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective fun x : U ↦ (hU.primeIdealOf x).asIdeal := by
  intro a b hab
  have h : hU.fromSpec (hU.primeIdealOf a) = hU.fromSpec (hU.primeIdealOf b) := by
    rw [PrimeSpectrum.ext hab]
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf, ← Subtype.ext_iff] at h

end AlgebraicGeometry
