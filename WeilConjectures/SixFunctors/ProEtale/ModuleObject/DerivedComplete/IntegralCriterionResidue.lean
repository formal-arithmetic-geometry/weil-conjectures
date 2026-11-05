/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralCriterion

/-!
# The integral constructibility criterion with condensed residue coefficients

A variant of blueprint `sk-prop-integral-criterion`, (2) ⇒ (1)
(`ProEtale.boundedConstructible_of_derivedCompleteIntegers`), with the hypothesis on the
reduction stated for the condensed coefficient ring `𝔽_{E,X}`: on a noetherian scheme `X`, a
derived complete complex `K` of `𝒪_{E,X}`-modules whose derived extension of scalars
`𝔽_{E,X} ⊗ᴸ K` is a bounded constructible complex of `𝔽_{E,X}`-modules is bounded constructible
(`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_residueField`). This is the form
in which the reduction of nearby cycles is controlled by the finiteness theorem with
finite coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

end AlgebraicGeometry.ProEtale
