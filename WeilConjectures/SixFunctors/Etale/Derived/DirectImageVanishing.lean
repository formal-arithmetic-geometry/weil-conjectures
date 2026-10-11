/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyModules
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.SixFunctors.Etale.Gabber
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-!
# Vanishing of the higher direct images above twice the dimension

Let `k` be a separably closed field, `f : X ⟶ Y` a morphism of finite type between `k`-schemes
locally of finite type, with `dim X ≤ d`, and `Λ` a finite ring. Then `R^q f_* M = 0` for every
`q > 2d` and every étale sheaf `M` of `Λ`-modules on `X`
(`AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul`, blueprint
`lem-sf-etale-direct-image-vanishing`).

The proof follows the blueprint. The sheaf `R^q f_* M` is the sheafification of the presheaf
`W ↦ H^q(W ×_Y X, M|)` on `Y_ét` (`AlgebraicGeometry.Etale.isLocallyBijective_higherDirectImagePresheafToSheaf`),
so it suffices that these groups vanish for affine `W`. Then `W ×_Y X` is a `k`-scheme of finite
type, étale over `X`, hence of dimension at most `d`, and its torsion cohomological dimension is
at most `2d` (`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`, blueprint
`sk-prop-sf-finiteness`). That bound is stated for abelian sheaves; it is transported to sheaves
of `Λ`-modules by dimension shifting
(`AlgebraicGeometry.Etale.subsingleton_ext_freeSheaf_of_subsingleton_H`), using that the
underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic
(`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`).

## Main definitions

- `AlgebraicGeometry.Etale.HasUniformDirectImageVanishingLE`: the bound `UDV(f, Λ; N)` of
  blueprint `def-sf-uniform-direct-image-vanishing`.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_ext_freeSheaf_of_subsingleton_H`: the cohomology of a
  sheaf of `Λ`-modules over an étale `X`-scheme `V` vanishes in a degree where the abelian
  cohomology of its underlying abelian sheaf restricted to `V` does.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_isAffine`: `R^q h_* K = 0` as soon
  as `H^q(W ×_X Y, K|) = 0` for every affine `W` étale over `X`.
- `AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul`: blueprint
  `lem-sf-etale-direct-image-vanishing`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `def-sf-uniform-direct-image-vanishing`: Uniform vanishing of the higher direct
images.

`UDV(f, Λ; N)` holds if the higher direct images of `f` on the small étale sites vanish above
`N` for every sheaf of `Λ`-modules: `R^q f_* M = 0` for every `q > N` and every étale sheaf `M`
of `Λ`-modules on `X`. -/
def Etale.HasUniformDirectImageVanishingLE {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ) : Prop :=
  ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), (N : ℤ) < q →
    IsZero (Etale.higherDirectImage Λ f q M)

end AlgebraicGeometry
