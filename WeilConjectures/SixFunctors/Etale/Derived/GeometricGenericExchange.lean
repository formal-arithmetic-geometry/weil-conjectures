/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GeometricGenericFibre

/-!
# Geometric generic restriction and exceptional restriction to a closed subscheme

Over a smooth integral curve `B`, pullback `g` to the geometric generic fibre commutes with
the exceptional restriction `Ri^!` along a closed immersion `i`
(`lem-weil-geometric-generic-exchange`).
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

Let `B` be a smooth integral curve over `k`, `η̄` its geometric generic point and `g` the
geometric generic pullback on `B`-schemes of finite type. For a closed immersion `i : Z ⟶ X`
of `B`-schemes and `M ∈ Dᵇc(X, Λ)`, the exceptional restriction commutes with `g`:
`g_Z^* Ri^! M ≅ Ri_{η̄}^! g_X^* M`. -/
theorem nonempty_iso_leftDerivedUpperStar_rightDerivedUpperShriek_geometricGenericPoint
    {X Z : Scheme.{u}} (πX : X ⟶ B) [LocallyOfFiniteType πX] [QuasiCompact πX] (i : Z ⟶ X)
    [IsClosedImmersion i]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((L((pullback.fst (i ≫ πX) B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj M) ≅
      (R(geometricGenericFibreMap i rfl)^![ModuleCat.{u + 1} Λ]).obj
        ((L((pullback.fst πX B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])).obj M)) :=
  sorry

end Exchange

end Etale

end AlgebraicGeometry
