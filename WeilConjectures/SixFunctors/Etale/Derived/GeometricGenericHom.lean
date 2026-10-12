/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GeometricGenericExchange

/-!
# Geometric generic restriction and the internal hom

Over a smooth integral curve `B`, pullback `g` to the geometric generic fibre commutes with
the internal hom `RHom(K, -)` for `K ∈ Dctf` (`lem-weil-geometric-generic-exchange`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]


section Exchange

variable {B : Scheme.{u}} [IsIntegral B] (b : B ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 b]

include b

/-- Blueprint `lem-weil-geometric-generic-exchange`: Restriction to the geometric generic fibre.

Let `B` be a smooth integral curve over `k`, `η̄` its geometric generic point and
`g : X_η̄ ⟶ X` the geometric generic pullback of a `B`-scheme `X` of finite type. For
`K ∈ Dctf(X, Λ)` and `M ∈ Dᵇc(X, Λ)`, the comparison map
`g^* RHom(K, M) ⟶ RHom(g^* K, g^* M)` of the monoidal functor `g^*` is an isomorphism. -/
theorem isIso_ihomComparison_geometricGenericPoint {X : Scheme.{u}} (πX : X ⟶ B)
    [LocallyOfFiniteType πX] [QuasiCompact πX]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ)
      (pullback.fst πX B.geometricGenericPoint)
    IsIso ((ihomComparison L((pullback.fst πX B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])
      K).natTrans.app M) :=
  sorry

end Exchange

end Etale

end AlgebraicGeometry
