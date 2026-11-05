/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-!
# Consecutive-quotient Tor and split universal coefficients

`levelTor I n M` is the degree `-1` homology of a projective resolution of an
`A/I^{n+2}`-module `M`, reduced to `A/I^{n+1}`. Over a principal ideal domain, a direct summand
of `H^q(P)` killed by `I^m` is a retract of `H^q(P ⊗ A/I^m)` for a complex `P` of finite
projective modules.

Source: Bhatt--Scholze, Proposition 6.6.11; step 5 of
`lem-weil-pbc-adic-tor-implies-flat-cohomology`
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ)

section

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (f : R →+* S)

end

end ModuleCat
