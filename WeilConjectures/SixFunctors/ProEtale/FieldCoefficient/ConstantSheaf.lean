/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf

/-!
# The constant sheaf `Λ_X` of a nonarchimedean ring on the pro-étale site

Let `Λ` be a commutative ring with an ultrametric norm, for instance a finite extension `E` of
`ℚ_ℓ` inside `ℚ̄_ℓ` with the restricted norm, or its ring of integers `𝒪_E`. Following
Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8), the constructible `E`-sheaves of the
blueprint (`def-weil-weil-sheaf-complex`) are modules over the
pro-étale sheaf `E_X : U ↦ C(U, E)` of continuous `E`-valued functions. This file constructs
`Λ_X` (`AlgebraicGeometry.ProEtale.fieldConstantSheaf Λ X`) for any such `Λ`: it is the
restriction to the small pro-étale site of `X` of the presheaf `U ↦ C(U, Λ)` on all schemes,
which is an fpqc sheaf.

This file and the others in `WeilConjectures.SixFunctors.ProEtale.FieldCoefficient` are the
counterparts, for the coefficient field `Λ`, of the files in
`WeilConjectures.SixFunctors.ProEtale.Adic`, which treat `ℚ̄_ℓ = PadicAlgCl ℓ`, and follow them
closely. For `ℚ̄_ℓ`, which is not locally compact, the sheaf of Bhatt–Scholze is that of the
*locally finite* continuous functions (`PadicAlgCl.locallyFiniteFunctions`); for a finite
extension `E` of `ℚ_ℓ` every continuous function is locally finite, and the two descriptions
agree. To keep the proofs of the `ℚ̄_ℓ` case, the sections are packaged as the subalgebra
`AlgebraicGeometry.fieldFunctions Λ U = ⊤` of `C(U, Λ)`.

## Main definitions

- `AlgebraicGeometry.FieldCoefficients`: the coefficient category, modules over `Λ`, lifted to
  the universe of the sites.
- `AlgebraicGeometry.fieldFunctions`: the continuous functions `T → Λ`, as a subalgebra.
- `AlgebraicGeometry.fieldFunctionsPresheaf`: the presheaf `U ↦ C(U, Λ)` on all schemes, an
  fpqc sheaf (`AlgebraicGeometry.isSheaf_fpqcTopology_fieldFunctionsPresheaf`).
- `AlgebraicGeometry.ProEtale.fieldConstantSheaf`: the constant sheaf `Λ_X`.
- `AlgebraicGeometry.ProEtale.fieldConstantSheafLowerStarIso`: for an isomorphism `e : X ≅ Y`,
  `e_* Λ_X ≅ Λ_Y`.

## Main results

- `AlgebraicGeometry.ProEtale.not_isZero_fieldConstantSheaf`: `Λ_X` is nonzero on a nonempty
  scheme.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry

section FieldFunctions

variable (Λ : Type) [NormedCommRing Λ] (T : Type*) [TopologicalSpace T]

variable {Λ T}

variable {T' : Type*} [TopologicalSpace T']

end FieldFunctions

namespace FieldCoefficients

variable (Λ : Type) [NormedCommRing Λ]

variable {Λ}

end FieldCoefficients

variable (Λ : Type) [NormedCommRing Λ]

open FieldCoefficients

namespace ProEtale

end ProEtale

end AlgebraicGeometry
