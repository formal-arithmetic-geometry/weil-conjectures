/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.CategoryTheory.Triangulated.FunctorCone
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars

/-!
# Descent of bounded constructible `ℚ̄_ℓ`-complexes: the cone step

Let `ℓ` be a prime and `X` a scheme. A complex `K ∈ D(ℚ̄_ℓ,X)` *descends* to a finite
subextension (`ProEtale.descendsToPadicSubfield X ℓ K`) if `K ≅ T^X_{E,Ω} K_E` for some finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and some bounded constructible `K_E ∈ D(E_X)`.

This property is closed under isomorphisms and shifts, and, on a topologically noetherian `X`
and assuming **(Hom)**-surjectivity, under extensions: if `K' ⟶ K ⟶ K'' ⟶ K'[1]` is
distinguished and `K'`, `K''` descend, then so does `K`
(`ProEtale.descendsToPadicSubfield_obj₂`, the cone step of blueprint
`det-lem-coefficient-finite-descent-objects`). Indeed, the connecting morphism
`K'' ⟶ K'[1]`, transported, descends by (Hom) to some `δ_H` over a common finite subextension
`H`, and the cone of `δ_H` is bounded constructible and descends `K` by TR3 and the five lemma
(`CategoryTheory.Functor.exists_distinguished_iso_obj₂_of_iso`).

The extensions of scalars being exact, their left derived functors are isomorphic to the
triangulated functors `Functor.mapDerivedCategory`
(`Functor.leftDerivedFunctorIsoMapDerivedCategory`), through which they commute with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

end AlgebraicGeometry.ProEtale
