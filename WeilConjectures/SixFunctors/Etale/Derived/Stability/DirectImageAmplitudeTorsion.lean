/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotientCoefficients

/-!
# Amplitude of the direct image of complexes killed by an integer

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, and
`Λ` an arbitrary commutative ring. The bound `Rf_* D^{≤ n} ⊆ D^{≤ n + 2d}` of
`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj` assumes `Λ` torsion. This file proves
it for bounded complexes killed by a nonzero integer `N`
(`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj_of_nsmul_id_eq_zero`):

* a sheaf `F` of `Λ`-modules killed by `N` is the restriction of scalars of a sheaf of
  `Λ ⧸ N`-modules, and restriction of scalars commutes with `Rf_*`
  (`AlgebraicGeometry.Etale.restrictScalarsRightDerivedLowerStarSingleIso`); the ring `Λ ⧸ N` is
  torsion, so `Rf_* F` vanishes above `2d`;
* a bounded complex killed by `N` has its homology sheaves killed by `N`, and the dévissage
  `DerivedCategory.isLE_obj_of_isLE_of_homologyProperty` concludes.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k))
  (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
  [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) (d : ℕ)
  (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))

end Etale

end AlgebraicGeometry
