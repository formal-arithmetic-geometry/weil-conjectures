/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-!
# The internal hom of `Λ_X`-modules is local

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

The internal hom `𝓗om_{Λ_X}(M, N)` of sheaves of `Λ_X`-modules is the equalizer of
`[M, N] ⇉ [Λ_X ⊗ M, N]` (`AlgebraicGeometry.ProEtale.FieldSheaf.ihomIsoIhom'`). Pullback along a
weakly étale morphism `g` commutes with the internal hom of sheaves and with equalizers, so it
commutes with `𝓗om_{Λ}` (`AlgebraicGeometry.ProEtale.fieldUpperStarIhomIso`):
`g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

attribute [local instance] Sheaf.symmetricCategory

namespace FieldSheaf

end FieldSheaf

variable {V X : Scheme.{u}} (g : V ⟶ X) [WeaklyEtale g]

end AlgebraicGeometry.ProEtale
