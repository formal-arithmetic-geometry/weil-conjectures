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
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme
namespace Etale

/-- Faithfulness of algebraic-closure pullback on the ordinary finite-coefficient derived category.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-
duality/sec-verdier-biduality/sk-thm-pd-verdier-duality/det-pd-biduality-coefficients.proof.md`,
Proof (i), finite-base-field paragraph (blueprint:
`lem-sf-finite-ring-geometric-duality-finite-field`).

The proof uses faithful exact pullback of constant coefficient module sheaves, its termwise
triangulated derived factorization, and reflection of acyclic cones. This is independent of the
base-change comparison obligation and is left as a separate stage-3 proof obligation. -/
theorem finiteField_biduality_algebraicClosure_pullback_reflects
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k : Type u) [Field k] [Finite k] [CharP k p]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : A, (ell ^ r) • x = 0)
    {T : Scheme.{u}} (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    let kbar := AlgebraicClosure k
    let b := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
    let X := pullback a b
    let g : X ⟶ T := pullback.fst a b
    (L((g)^*[ModuleCat.{u + 1} A])).ReflectsIsomorphisms := by
  sorry

end Etale
end AlgebraicGeometry
