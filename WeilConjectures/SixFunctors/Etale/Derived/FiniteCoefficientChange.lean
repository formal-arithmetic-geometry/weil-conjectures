/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude

/-!
# Finite coefficient change for the ordinary direct image

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, `A` a
finite coefficient ring and `J` an ideal of `A`, with quotient `B = A ⧸ J`. For `K ∈ D(X_ét, A)`
bounded above (for instance `K ∈ D^b_{ctf}(X, A)`), the coefficient change map

`c_{f,K} : (Rf_* K) ⊗ᴸ_A B_Y ⟶ Rf_*(K ⊗ᴸ_A B_X)`

is an isomorphism (blueprint `lem-coef-finite-direct-image`). As elsewhere in the repository
(`AlgebraicGeometry.Etale.reductionModIdeal`), the `B`-module objects are recorded through their
restriction of scalars to `A`, the reduction `K ↦ K ⊗ᴸ_A B_X` being
`AlgebraicGeometry.Etale.reductionModIdeal`; the map `c_{f,K}` is
`AlgebraicGeometry.Etale.rightDerivedLowerStarReductionModIdealMap`, the projection map of `Rf_*`
at `(K, B_Y)` followed by `Lf^* B_Y ≅ B_X`. It is natural in `K`, being a natural
transformation.

The proof is the blueprint's: `B` is a finitely generated `A`-module, and the projection formula
with a finitely presented constant coefficient
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle`,
blueprint `lem-sf-projection-finite-constant`) is proved there by the way-out argument along
the syzygies of `B`, using that `Rf_*` raises degrees by at most `2d`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarReductionModIdealMap_app_of_finite`
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar_of_finite`
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (J : Ideal Λ) {k : Type u} [Field k]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
  (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))

omit [Finite Λ] in
/-- The comparison `Rg_*M ⊗ᴸ N_Y ⟶ Rg_*(M ⊗ᴸ N_Z)` attached to an isomorphism
`a : Lg^*N_Y ≅ N_Z` is an isomorphism at `M` as soon as the projection map of `Rg_*` is an
isomorphism at `(M, N_Y)`. -/
lemma isIso_rightDerivedLowerStarDerivedTensorRightMap_app {Z : Scheme.{u}} (g : Z ⟶ Y)
    {NY : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {NZ : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : L((g)^*[ModuleCat.{u + 1} Λ]).obj NY ≅ NZ)
    {M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app M).app NY)) :
    IsIso ((rightDerivedLowerStarDerivedTensorRightMap _ g a.hom).app M) :=
  IsIso.comp_isIso' h inferInstance

include hf hd in
/-- Blueprint `lem-coef-finite-direct-image`: Finite coefficient change for ordinary direct
image.

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, `Λ` a
finite ring, `J` an ideal of `Λ` and `K ∈ D(X_ét, Λ)` bounded above. Then the coefficient change
map `c_{f,K} : (Rf_* K) ⊗ᴸ (Λ ⧸ J)_Y ⟶ Rf_*(K ⊗ᴸ (Λ ⧸ J)_X)`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarReductionModIdealMap`, natural in `K`) is an
isomorphism: it is the projection map of `Rf_*` at the finitely generated constant coefficient
`Λ ⧸ J`, followed by `Lf^*(Λ ⧸ J)_Y ≅ (Λ ⧸ J)_X`. -/
theorem isIso_rightDerivedLowerStarReductionModIdealMap_app_of_finite
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (b : ℤ)
    [K.IsLE b] : IsIso ((rightDerivedLowerStarReductionModIdealMap Λ J f).app K) :=
  isIso_rightDerivedLowerStarDerivedTensorRightMap_app _ f _
    (isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle Λ aX aY f hf d hd K b _)

include hf hd in
/-- Blueprint `lem-coef-finite-direct-image`: Finite coefficient change for ordinary direct
image, as an isomorphism `Rf_* K ⊗ᴸ (Λ ⧸ J)_Y ≅ Rf_*(K ⊗ᴸ (Λ ⧸ J)_X)` of reductions
(`AlgebraicGeometry.Etale.reductionModIdeal`), for a finite ring `Λ`, a morphism `f` of
`k`-schemes of finite type and `K ∈ D(X_ét, Λ)` bounded above. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerStar_of_finite
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (b : ℤ)
    [K.IsLE b] :
    Nonempty ((reductionModIdeal Λ Y J).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((reductionModIdeal Λ X J).obj K)) :=
  have := isIso_rightDerivedLowerStarReductionModIdealMap_app_of_finite Λ J aX aY f hf d hd K b
  ⟨asIso ((rightDerivedLowerStarReductionModIdealMap Λ J f).app K)⟩

end Etale

end AlgebraicGeometry
