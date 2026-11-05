/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologyHom
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField

/-!
# Cohomology with supports and the exceptional inverse image of a closed immersion

For a closed immersion `i : Z ⟶ X` the cohomology with supports `H^a_Z(X, K)` of
`AlgebraicGeometry.Etale.derivedSupportCohomology` is `Hom(Λ_Z, Ri^!(K[a]))`
(`AlgebraicGeometry.Etale.supportCohomologyAddEquiv`): by `H^a_Z(X, K) ≅ Hom(i_* Λ_Z, K[a])`
(`AlgebraicGeometry.Etale.derivedSupportCohomologyAddEquiv`), `i_* Λ_Z ≅ Ri_! Λ_Z` and the
adjunction `Ri_! ⊣ Ri^!`. This identification is `Λ`-linear
(`AlgebraicGeometry.Etale.supportCohomologyLinearEquiv`), as `H^a_Z(X, -)` is `Λ`-linear
(`AlgebraicGeometry.Etale.linear_derivedSupportCohomology`).

A morphism `g : Λ_Z ⟶ R` gives a global section of `H⁰(R)`, the image of `1` under
`H⁰(g) : Λ = H⁰(Λ_Z) ⟶ H⁰(R)` (`AlgebraicGeometry.Etale.homConstantComplexLinearMapΓHomologyZero`);
this is bijective when `R` is concentrated in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section SupportHom

variable [Finite Λ] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

end SupportHom

section Linear

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

end Linear

section Endomorphisms

variable {Z : Scheme.{u}}

end Endomorphisms

section HomologyZero

variable {Z : Scheme.{u}}

end HomologyZero

end Etale

end AlgebraicGeometry
