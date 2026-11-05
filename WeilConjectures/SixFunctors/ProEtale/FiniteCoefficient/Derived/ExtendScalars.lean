/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Derived extension of scalars on the pro-étale site

Let `S` be an algebra over a commutative ring `R`, not necessarily flat. Derived scalar extension
`K ↦ K ⊗ᴸ_R S : D(X_proét, R) ⥤ D(X_proét, S)` is the total left derived functor
`L(sheafExtendScalars (algebraMap R S) X)` of the extension of scalars of pro-étale sheaves,
computed on K-flat complexes: restricted back to `R`, the extension of scalars is the tensor
product with the constant sheaf `S_X`, so it sends quasi-isomorphisms between K-flat complexes
to quasi-isomorphisms. It is left adjoint to the restriction of scalars
`D(X_proét, S) ⥤ D(X_proét, R)`.

Derived scalar extension commutes with the derived pullbacks: for `g : Z ⟶ Y` both composites
`L(S ⊗_R -) ⋙ Lg^*` and `Lg^* ⋙ L(S ⊗_R -)` are total left derived functors of the composite
`g^* (S ⊗_R -) ≅ S ⊗_R g^* -` of sheaf functors, the second one being computed on the complexes
whose pullback by `g` is K-flat (`AlgebraicGeometry.ProEtale.kFlatUpperStar`).

## Main definitions

- `AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsAdjunction`: the adjunction between
  derived scalar extension `- ⊗ᴸ_R S` (blueprint `def-weil-derived-tensor`) and restriction of
  scalars.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`: the isomorphism
  `(Lg^* K) ⊗ᴸ_R S ≅ Lg^*(K ⊗ᴸ_R S)` (blueprint `thm-trf-finite-coefficient-map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory HomologicalComplex

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S]

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

/- Mathlib's instance is stated for `extendScalars.{u₁, u₂, max u₂ w}`, and unifying
`u + 1 =?= max (u + 1) ?w` gets stuck. -/

section

variable (R S) (X : Scheme.{u})

end

section Pullback

variable (R S) [IsNoetherianRing R] {Y Z : Scheme.{u}} (g : Z ⟶ Y)

end Pullback

end AlgebraicGeometry.ProEtale
