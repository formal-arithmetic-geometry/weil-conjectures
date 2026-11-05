/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterionStep

/-!
# Deligne's finiteness criterion at closed points

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, and
`p : X ⟶ Spec k` proper. Let `hᵢ : Wᵢ ⟶ X` be finitely many morphisms from Noetherian schemes
whose images contain all the non-closed points of `X`. A bounded below complex `G` of étale
sheaves of `Λ`-modules on `X` is bounded constructible as soon as its pullbacks `Lhᵢ^* G` and its
cohomology `Rp_* G` are bounded constructible
(`AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar_of_isProper`).

This is the form of Deligne's argument (SGA 4½, [Th. finitude], proof of 3.2) used for the
finiteness of nearby cycles, the `hᵢ` being the geometric generic fibres of the coordinates of
the charts of the special fibre of `ℙⁿ`.

## Proof

Let `F = ℋ^q(G)`. By Deligne's approximation
(`AlgebraicGeometry.Etale.exists_mono_isConstructibleSheaf_isZero_sheafFiber_cokernel`) it has a
constructible subsheaf `F₀` with `F / F₀` supported at closed points; for `q` larger than the
amplitudes of the `Lhᵢ^* G`, `F` itself is supported at closed points.
* By induction on `q` from below, `τ^{≤ q} G` is bounded constructible: if `τ^{< q} G` is, so is
  its cohomology (`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper`),
  hence `H^q(X, τ^{≥ q} G) = Γ(X, F)` is finite
  (`AlgebraicGeometry.Etale.nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE`);
  then `Γ(X, F / F₀)` is finite, as `H¹(X, F₀)` is, so `F / F₀` is constructible
  (`AlgebraicGeometry.Etale.isConstructibleSheaf_of_isZero_sheafFiber_of_finite`), and so is `F`.
* For `N` beyond the amplitudes, `τ^{≥ N} G` has cohomology sheaves supported at closed points,
  which are acyclic
  (`AlgebraicGeometry.Etale.isZero_homology_rightDerivedGlobalSections_of_isZero_sheafFiber`), so
  `H^q(X, τ^{≥ N} G) = Γ(X, ℋ^q(G))` vanishes for large `q`, and `ℋ^q(G) = 0` for large `q`
  (`AlgebraicGeometry.Etale.isZero_of_isZero_sheafFiber_of_subsingleton`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory.TStructure (t)

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

end Etale

end AlgebraicGeometry
