/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.DualizingComplexId
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Verdier biduality at a separably closed point

For a separably closed field `k`, the double-dual morphism of `Spec k` over itself is an
isomorphism on `Dctf(Spec k, Λ)` (blueprint `lem-weil-coefficient-frobenius`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-weil-coefficient-frobenius`, at the separably closed point: for a separably
closed field `k` and `K ∈ Dctf(Spec k, Λ)`, the double-dual morphism `K ⟶ 𝔻 𝔻 K` of the point
`Spec k` over itself is an isomorphism: under `RΓ(Spec k, -)` it is derived evaluation into the
coefficient double dual of a perfect complex of `Λ`-modules. -/
theorem isIso_verdierDualDoubleDual_app_id_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    {K : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k)) K) :
    IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) (𝟙 (Spec (.of k)))).app K) :=
  sorry

end Etale

end AlgebraicGeometry
