/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# `ModuleCat.{v} R` is Grothendieck abelian for a `v`-small ring `R`

Mathlib states `AB5 (ModuleCat.{u} R)` and `IsGrothendieckAbelian.{u} (ModuleCat.{u} R)`
only for `R : Type u`, i.e. when the modules live in the same universe as the ring. Sheaves
on the pro-étale site of a scheme in `Scheme.{u}` need coefficients in `Type (u + 1)` while
the coefficient ring `𝒪_E` stays in `Type u`, so we need the statements for
`ModuleCat.{v} R` with `[Small.{v} R]`. The proofs are those of Mathlib verbatim.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

variable (R : Type u) [Ring R]

instance ModuleCat.ab5 : AB5 (ModuleCat.{v} R) where
  ofShape J _ _ :=
    HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})

instance ModuleCat.isGrothendieckAbelian [Small.{v} R] :
    IsGrothendieckAbelian.{v} (ModuleCat.{v} R) where
