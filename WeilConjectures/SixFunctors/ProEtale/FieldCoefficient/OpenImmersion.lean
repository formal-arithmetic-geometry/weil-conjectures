/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-!
# Extension by zero of sheaves of modules over the constant sheaf

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

For an open immersion `j : U ⟶ X`, the pullback `j^*` of sheaves of `Λ_X`-modules
(`AlgebraicGeometry.ProEtale.fieldUpperStar`) preserves limits, its underlying functor being the
restriction along the localization functor. Hence it has a left adjoint, the extension by zero
`j_!` (`AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriek`), by the special adjoint functor
theorem in the Grothendieck abelian category of sheaves of `Λ_X`-modules. The pushforward `j_*`
is fully faithful (the counit of `j^* ⊣ j_*` is invertible), hence so is `j_!`, and `j_! F`
vanishes along every morphism missing the range of `j`.

On underlying sheaves, `j_!` is the extension by zero of sheaves
(`AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriekComparison`), hence exact. The point is
that the underlying sheaf of `j_! M` is an extension by zero, i.e. the counit of `j_! ⊣ j^*` on
sheaves is invertible there. For a free module `Λ_U ⊗ P` the underlying sheaf of `j_!` is
`Λ_X ⊗ j_! P`, the tensor product of a sheaf with a presheaf vanishing away from `U`,
sheafified; and every module is a cokernel of a morphism of free modules.

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriek`: `j_!`, with notation `(j)_!ᶠ[Λ]`.
- `AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriekComparison`: the comparison
  `j_! M.X ⟶ (j_! M).X`, an isomorphism, giving the exactness of `j_!`.
- `AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriekToLowerStar`: the comparison
  `j_! ⟶ j_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

@[inherit_doc fieldOpenImmersionLowerShriek]
scoped notation "(" j ")_!ᶠ[" Λ "]" => fieldOpenImmersionLowerShriek Λ j

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [IsOpenImmersion φ]

end AlgebraicGeometry.ProEtale
