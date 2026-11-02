/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme
namespace Etale

/-- Base-change isomorphism for finite-field Verdier biduality.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-
duality/sec-verdier-biduality/sk-thm-pd-verdier-duality/det-pd-biduality-coefficients.proof.md`,
Proof (i), finite-base-field paragraph (blueprint:
`lem-sf-finite-ring-geometric-duality-finite-field`).

The proof requires the evaluation-compatible comparison for separable algebraic extension,
preservation of constructibility and finite Tor amplitude under pullback, and the algebraically
closed geometric biduality theorem. These are independent geometric comparison obstacles and are
left as the declared stage-3 proof obligation. -/
theorem finiteField_biduality_baseChange
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k : Type u) [Field k] [Finite k] [CharP k p]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : A, (ell ^ r) • x = 0)
    {T : Scheme.{u}} (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    {L : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T L) :
    let kbar := AlgebraicClosure k
    let b := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
    let X := pullback a b
    let g : X ⟶ T := pullback.fst a b
    letI : HasCompactification a := (NagataCompactification a).hasCompactification
    IsIso ((L((g)^*[ModuleCat.{u + 1} A])).map
      ((verdierDualDoubleDual A a).app L)) := by
  sorry

end Etale
end AlgebraicGeometry
