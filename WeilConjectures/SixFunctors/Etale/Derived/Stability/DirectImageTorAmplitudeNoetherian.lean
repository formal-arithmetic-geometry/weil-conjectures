/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImageAmplitudeTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.TorAmplitudeFiniteConstant

/-!
# The direct image of a complex of finite Tor amplitude, Noetherian coefficients

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, and
`Λ` a Noetherian ring. If `K ∈ D(X_ét, Λ)` has Tor amplitude in `[a, b]` and is killed by a
nonzero integer `N`, then `Rf_* K` has Tor amplitude in `[a, b + 2d]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_nsmul_id_eq_zero`). This is the
case of blueprint `sk-thm-sf-direct-image-tor-amplitude` used at the integral coefficient stage.

The proof follows the one for finite coefficients
(`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_finite`), with two changes:

* the bound `Rf_* D^{≤ n} ⊆ D^{≤ n + 2d}` is only available for bounded complexes killed by `N`
  (`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj_of_nsmul_id_eq_zero`); the complexes
  `K ⊗ᴸ M_X` met in the way-out argument proving the projection formula for a finitely generated
  `M` (blueprint `lem-sf-projection-finite-constant`) are of this kind, by the Tor amplitude of
  `K`;
* the residue test is replaced by the test on finitely generated constant sheaves
  (`AlgebraicGeometry.Etale.torAmplitudeIn_of_forall_finite_constantSheaf`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] {X Y : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) (d : ℕ)
  (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))

end Etale

end AlgebraicGeometry
