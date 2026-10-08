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

/-- **The Stein factorization** of a morphism `p : Y ⟶ Spec R`: with `B = Γ(Y, 𝒪_Y)`, an
`R`-algebra through `p`, the morphism `p` factors as
`Y ⟶ Spec B ⟶ Spec R`, the first map being the canonical morphism `Y.toSpecΓ` and the second
the morphism `Spec B ⟶ Spec R` of the algebra structure
(`AlgebraicGeometry.Scheme.toSpecΓ_steinFactorizationBase`). For a proper `p` this is the Stein
factorization [Stacks 03GX].
(blueprint: `def-weil-pbc-stein-factorization`) -/
noncomputable def Scheme.Hom.steinFactorizationBase {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (p : Y ⟶ Spec R) : Spec Γ(Y, ⊤) ⟶ Spec R :=
  Spec.map ((Scheme.ΓSpecIso R).inv ≫ p.appTop)

/-- The Stein factorization `Y ⟶ Spec Γ(Y, 𝒪_Y) ⟶ Spec R` of `p : Y ⟶ Spec R` composes to
`p`. -/
@[reassoc (attr := simp)]
lemma Scheme.toSpecΓ_steinFactorizationBase {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (p : Y ⟶ Spec R) : Y.toSpecΓ ≫ p.steinFactorizationBase = p := by
  rw [Scheme.Hom.steinFactorizationBase, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

end AlgebraicGeometry
