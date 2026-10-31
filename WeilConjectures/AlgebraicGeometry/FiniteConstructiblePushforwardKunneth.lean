/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.FiniteConstructibleDirectImage

/-!
# Finite constructible pushforward in the Künneth formula

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
`lem-kun-095r.md` (blueprint: lem-kun-095r).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A finite finitely presented morphism between finite-type schemes over a field sends
constructible module sheaves to constructible module sheaves, with no positive higher
direct images, for the finite coefficients of smooth base change.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
`lem-kun-095r.md` (blueprint: lem-kun-095r).

Proof: apply `finite_directImage_constructible_and_higher_vanishing`
(`lem-fin-finite-morphism`) with S = Y, the given field, finite morphism, coefficient ring
and constructible module sheaf; Y is of finite type over k. The coefficient integer is
invertible on Y because it is invertible on Spec k: map the unit along the ring
homomorphism `(Y ↘ Spec (.of k)).appTop`, which sends natural numbers to natural numbers.
Positivity, finiteness of Λ and the annihilation `(N : Λ) = 0` are unchanged. The cited
theorem gives exactly the two clauses: constructibility of f_*F and vanishing of every
positive-degree homology of the bounded-below right derived direct image of F[0]. -/
theorem finite_pushforward_constructible_and_higherDirectImage_vanish
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : @Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F) :
    @Scheme.IsConstructibleEtaleModuleSheaf Y Λ _ hcoeff.2.1
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ∧
    ∀ q : ℤ, 0 < q → IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  have hcoeffY : IsSmoothBaseChangeCoefficients N Λ Y :=
    ⟨hcoeff.1, hcoeff.2.1, hcoeff.2.2.1, by
      simpa only [map_natCast] using
        hcoeff.2.2.2.map (Y ↘ Spec (.of k)).appTop.hom⟩
  exact finite_directImage_constructible_and_higher_vanishing k f N Λ hcoeffY F hF

end AlgebraicGeometry.Etale
