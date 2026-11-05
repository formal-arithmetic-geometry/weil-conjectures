/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint

/-!
# Kummer covers in the pro-étale site

Let `A` be a ring, `f ∈ A` a unit and `r` a natural number invertible in `A`. The Kummer tower
of `f` is the sequence of étale `A`-algebras `A[T]/(T^{rⁿ} - f)`, with transition maps
`T ↦ T^{r^{m - n}}`; its colimit `A[f^{1/r^∞}]` (`AlgebraicGeometry.ProEtale.kummerRing`) is
ind-étale, hence weakly étale, and integral and faithful over `A`, hence surjective on spectra.

For an affine open `U` of a scheme `X` and `f ∈ Γ(X, U)ˣ`, this gives an object
`AlgebraicGeometry.Scheme.ProEt.kummerCover` of `X_proét` with underlying scheme
`Spec Γ(X, U)[f^{1/r^∞}]` and image `U`. Finitely many of these, over an affine open cover of
`X`, cover the terminal object of `X_proét`.

If `X` is integral and its function field `K` contains the `rᵐ`-th roots of unity, then for every
morphism `g` from the geometric generic point to a Kummer cover (or to an object over a Kummer
cover) and every `σ ∈ Gal(Kˢᵉᵖ/K)` fixing `g`, `σ` fixes every `rᵐ`-th root of `f` in `Kˢᵉᵖ`.

## Main definitions

- `AlgebraicGeometry.ProEtale.kummerRing`: the ring `A[f^{1/r^∞}]`, with the compatible roots
  `AlgebraicGeometry.ProEtale.kummerRoot f r m` of `f` of order `rᵐ`.
- `AlgebraicGeometry.Scheme.ProEt.kummerCover`: `Spec Γ(X, U)[f^{1/r^∞}] ⟶ U ⟶ X` in `X_proét`.

## Main statements

- `AlgebraicGeometry.ProEtale.indEtale_kummerRing`.
- `AlgebraicGeometry.ProEtale.surjective_comap_algebraMap_kummerRing`.
- `AlgebraicGeometry.Scheme.ProEt.range_kummerCover_hom`: the image of a Kummer cover is `U`.
- `AlgebraicGeometry.Scheme.ProEt.ofArrows_kummerCover_mem_topology`: Kummer covers over a
  finite affine open cover of `X` cover the terminal object of `X_proét`.
- `AlgebraicGeometry.Scheme.ProEt.genericPointSepAut_apply_eq_of_comp_kummerCover`: the Galois
  elements fixing a morphism from the geometric generic point to a Kummer cover fix the roots
  of `f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Polynomial

namespace AlgebraicGeometry

namespace ProEtale

section Ring

variable {A : Type u} [CommRing A] (f : A) (r : ℕ)

end Ring

end ProEtale

namespace Scheme.ProEt

section KummerCover

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (r : ℕ)

variable (hf : IsUnit f) (hr : IsUnit (r : Γ(X, U)))

end KummerCover

section Cover

variable {X : Scheme.{u}} {ι : Type*} {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i))
  (f : ∀ i, Γ(X, U i)) (r : ℕ)

end Cover
section FixedRoots

variable {X : Scheme.{u}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
  {f : Γ(X, U)} (hf : IsUnit f) {r : ℕ} (hr : IsUnit (r : Γ(X, U)))

end FixedRoots

end Scheme.ProEt

end AlgebraicGeometry
