/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# `Spec` of a restriction map and the canonical isomorphisms of affine opens

We record that `Spec` of a restriction map between affine opens intertwines the canonical
isomorphisms `Spec Γ(X, U) ≅ U` with the inclusion of opens, and that the algebra map
realizing `Γ(X, X.basicOpen f)` as a localization is the restriction map of the structure
sheaf.

For an arbitrary scheme `X` and a global section `x`, the basic open `X_x` maps canonically
to `Spec Γ(X, ⊤)_x`. We record this morphism and the induced map on global sections:

- `AlgebraicGeometry.Scheme.toSpecAway` — the morphism `X_x ⟶ Spec Γ(X, ⊤)_x`;
- `AlgebraicGeometry.Scheme.awayToBasicOpen` — the induced ring map
  `Γ(X, ⊤)_x ⟶ Γ(X_x, ⊤)`, which sends `a / x` to `AlgebraicGeometry.Scheme.divBasicOpen`.
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

section Away

variable (X : Scheme.{u}) (x : Γ(X, ⊤))

/-- The canonical morphism `X_x ⟶ Spec Γ(X, ⊤)_x` from the locus where a global section does
not vanish to the spectrum of the localization of the global sections away from it. -/
noncomputable def Scheme.toSpecAway :
    (X.basicOpen x : Scheme.{u}) ⟶ Spec (.of <| Localization.Away x) :=
  X.toSpecΓ.resLE _ (X.basicOpen x) (X.toSpecΓ_preimage_basicOpen x).ge ≫
    (basicOpenIsoSpecAway x).hom

@[reassoc]
lemma Scheme.toSpecAway_SpecMap_algebraMap :
    X.toSpecAway x ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))) =
      (X.basicOpen x).ι ≫ X.toSpecΓ := by
  rw [Scheme.toSpecAway, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  exact Scheme.Hom.resLE_comp_ι ..

/-- The canonical map `Γ(X, ⊤)_x ⟶ Γ(X_x, ⊤)` from the localization of the global sections
away from `x` to the sections over the basic open `X_x`. -/
noncomputable def Scheme.awayToBasicOpen :
    CommRingCat.of (Localization.Away x) ⟶ Γ((X.basicOpen x : Scheme.{u}), ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (X.toSpecAway x).appTop

lemma Scheme.awayToBasicOpen_apply (y : Localization.Away x) :
    X.awayToBasicOpen x y = (X.toSpecAway x).appTop ((Scheme.ΓSpecIso _).inv y) :=
  rfl

lemma Scheme.algebraMap_comp_awayToBasicOpen :
    CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x)) ≫ X.awayToBasicOpen x =
      (X.basicOpen x).ι.appTop := by
  rw [Scheme.awayToBasicOpen, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Hom.comp_appTop, Scheme.toSpecAway_SpecMap_algebraMap, Scheme.Hom.comp_appTop,
    ← Category.assoc, Scheme.toSpecΓ_appTop]
  rw [show (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) : Type u))).inv ≫
    (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ from Iso.inv_hom_id _, Category.id_comp]

@[simp]
lemma Scheme.awayToBasicOpen_algebraMap (a : Γ(X, ⊤)) :
    X.awayToBasicOpen x (algebraMap Γ(X, ⊤) (Localization.Away x) a) =
      (X.basicOpen x).ι.appTop a := by
  conv_rhs => rw [← Scheme.algebraMap_comp_awayToBasicOpen X x]
  rfl

@[simp]
lemma Scheme.awayToBasicOpen_mk' (a : Γ(X, ⊤)) (h : x ∈ Submonoid.powers x) :
    X.awayToBasicOpen x (IsLocalization.mk' (Localization.Away x) a ⟨x, h⟩) =
      X.divBasicOpen a x := by
  refine X.eq_divBasicOpen ?_
  rw [← X.awayToBasicOpen_algebraMap x x, ← X.awayToBasicOpen_algebraMap x a, ← map_mul,
    IsLocalization.mk'_spec]

end Away

end AlgebraicGeometry
