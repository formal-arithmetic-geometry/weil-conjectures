/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdicCompleteHomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleDerivedAdicComplete
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CountableProducts

/-!

# Bounded constructible integral complexes are derived complete

On a noetherian scheme `X`, a bounded constructible complex of `𝒪_{E,X}`-modules is derived
`ℓ`-adically complete (`ProEtale.isDerivedAdicComplete_of_boundedConstructible`): the derived
limit of the tower `⋯ --ℓ--> K --ℓ--> K` vanishes (`CategoryTheory.IsDerivedAdicComplete`). This
is the completeness half of the implication (1) ⇒ (2) of blueprint `sk-prop-integral-criterion`
(section `sec-proetale-coefficients`); the other half, that the first derived reduction is
bounded constructible, is `ProEtale.boundedConstructible_derivedReduction_obj`.

A complex is derived complete if and only if its cohomology objects are
(`DerivedCategory.isDerivedAdicComplete_iff_homology`, countable products of module objects being
exact), and constructible module objects are derived complete
(`ProEtale.isDerivedAdicComplete_of_isConstructibleModuleObject`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

end AlgebraicGeometry.ProEtale
