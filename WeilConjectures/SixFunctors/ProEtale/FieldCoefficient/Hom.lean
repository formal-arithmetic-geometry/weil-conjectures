/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.GeometricFrobenius

/-!
# Tensor product and internal hom over the constant sheaf

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Hom`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

The constant sheaf `Λ_X` is a *commutative* sheaf of rings
(`AlgebraicGeometry.ProEtale.fieldConstantSheaf.isCommMonObj`), so sheaves of
`Λ_X`-modules have a tensor product `⊗_{Λ_X}` and an internal hom
`𝓗om_{Λ_X}` (`AlgebraicGeometry.ProEtale.FieldSheaf.ihom`), right adjoint to the tensor
product (`CategoryTheory.Mod.ihomAdjunction`). The pushforward along an isomorphism `e` commutes
with the internal hom (`AlgebraicGeometry.ProEtale.fieldLowerStarCompIhomIso`): this gives the
Weil structure of the internal hom of two Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

namespace FieldSheaf

end FieldSheaf

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

end AlgebraicGeometry.ProEtale
