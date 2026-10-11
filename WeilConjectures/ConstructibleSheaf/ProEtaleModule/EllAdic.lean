/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!

# Bounded constructible `ℓ`-adic complexes form a triangulated subcategory

Let `X` be a topologically noetherian scheme, `ℓ` a prime and `E ⊆ ℚ̄_ℓ` a finite subextension
of `ℚ_ℓ` (`PadicAlgCl.FiniteIntermediateField ℓ`) with ring of integers `𝒪_E`. This file states
that the bounded constructible complexes `ProEtale.boundedConstructible R` of
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` form a triangulated
subcategory of `D(Mod_R)` for the `ℓ`-adic coefficient ring objects `R = Λ_X = p_X^* Λ`
(`ProEtale.condensedRingObj`):

* `𝒪_E`-coefficients, `Λ = Profinite.padicIntegersRingObj ℓ E`
  (`ProEtale.isTriangulated_boundedConstructible_padicIntegers`);
* `E`-coefficients, `Λ = Profinite.continuousMapRingObj E`
  (`ProEtale.isTriangulated_boundedConstructible_padicSubfield`);
* `ℚ̄_ℓ`-coefficients, `Λ = Profinite.padicAlgClRingObj ℓ`
  (`ProEtale.isTriangulated_boundedConstructible_padicAlgCl`).

It is a property of these coefficient rings, not of a general ring object: it rests on the
constructible sheaves on `X` being closed under kernels, cokernels and extensions, which uses
that `𝒪_E` is noetherian and that `E` and `ℚ̄_ℓ` are obtained from it by inverting `ℓ` and by a
filtered colimit (Bhatt–Scholze, Section 6.8).

## Sorried input

All three instances are `sorry`ed: the closure of constructible sheaves under kernels, cokernels
and extensions is not formalized.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] (ℓ : ℕ) [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- On a topologically noetherian scheme, the bounded constructible complexes of
`𝒪_{E,X}`-modules form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_padicIntegers :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)).IsTriangulated :=
  sorry

/-- On a topologically noetherian scheme, the bounded constructible complexes of `E_X`-modules
form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_padicSubfield :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X)).IsTriangulated :=
  sorry

/-- On a topologically noetherian scheme, the bounded constructible complexes of
`ℚ̄_ℓ,X`-modules form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_padicAlgCl :
    (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).IsTriangulated :=
  sorry

end AlgebraicGeometry.ProEtale
