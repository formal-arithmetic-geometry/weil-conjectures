/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# The canonical morphism from a basic open to the spectrum of a localization

We record that the canonical morphism `X.basicOpen x ⟶ Spec Γ(X, ⊤)[1/x]`, obtained by
restricting `X.toSpecΓ` to the basic open `D(x)` of `Spec Γ(X, ⊤)`, is compatible with the
localization map `Γ(X, ⊤) ⟶ Γ(X, ⊤)[1/x]`.

We also record the full faithfulness of `Spec` in terms of bundled ring homomorphisms
(`AlgebraicGeometry.Spec.ringHomEquiv`), a variant of `AlgebraicGeometry.Spec.homEquiv`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical morphism `X.basicOpen x ⟶ Spec Γ(X, ⊤)[1/x]`, composed with `Spec` of the
localization map, is the composite `X.basicOpen x ⟶ X ⟶ Spec Γ(X, ⊤)`. -/
@[reassoc]
lemma resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap (X : Scheme.{u}) (x : Γ(X, ⊤)) :
    X.toSpecΓ.resLE (PrimeSpectrum.basicOpen x) (X.basicOpen x)
        (X.toSpecΓ_preimage_basicOpen x).ge ≫ (basicOpenIsoSpecAway x).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))) =
      (X.basicOpen x).ι ≫ X.toSpecΓ := by
  rw [basicOpenIsoSpecAway_hom_SpecMap, Scheme.Hom.resLE_comp_ι]

/-- **`Spec` is fully faithful**, in terms of bundled ring homomorphisms: the morphisms
`Spec S ⟶ Spec R` are the ring homomorphisms `R →+* S`. This is `Spec.homEquiv` composed with
the equivalence between the morphisms of `CommRingCat` and the bundled ring homomorphisms. -/
@[simps]
noncomputable def Spec.ringHomEquiv {R S : CommRingCat.{u}} : (Spec S ⟶ Spec R) ≃ (R →+* S) where
  toFun u := (Spec.preimage u).hom
  invFun t := Spec.map (CommRingCat.ofHom t)
  left_inv u := by simp
  right_inv t := by simp

end AlgebraicGeometry
