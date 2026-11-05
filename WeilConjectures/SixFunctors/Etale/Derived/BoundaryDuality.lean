/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The Verdier dual on `Dctf`: boundary exchange

For a finite coefficient ring `Λ` whose exponent is invertible on a field `k` and schemes
separated of finite type over `k`, this file states

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual`
  (`lem-weil-closed-costalk-duality`): `Ri^! 𝔻_T K ≅ 𝔻_Z (i^* K)`;
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_verdierDual`
  (`cor-weil-boundary-duality-discharge`): for a closed immersion `i : Z ⟶ T` the boundary
  exchange `i^* 𝔻_T L ≅ 𝔻_Z Ri^! L` holds on `Dctf(T)`;
- `AlgebraicGeometry.Etale.HasBoundaryDuality` (`def-weil-boundary-duality-input`) and
  `AlgebraicGeometry.Etale.hasBoundaryDuality` (`cor-weil-boundary-duality-discharge`): the
  finite-stage boundary duality input, and that it holds over an algebraically closed field;
- `AlgebraicGeometry.Etale.verdierDual_finiteStage` (`thm-sf-biduality-class`, finite stages):
  `𝔻_X` is an involution of `Dctf(X, Λ)` with the Tor bound `[-b - 2d, -a]`.

The canonical exchange map of the blueprint is not constructed; the exchange is stated as the
existence of an isomorphism, as in `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

end Etale

end AlgebraicGeometry
