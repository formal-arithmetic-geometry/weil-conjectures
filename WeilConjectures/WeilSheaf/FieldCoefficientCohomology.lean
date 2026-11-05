/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.OpenImmersion
public import WeilConjectures.WeilSheaf.FieldCoefficient
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Ordinary and compactly supported cohomology with coefficients in a finite extension of `ℚ_ℓ`

Let `Λ` be a commutative ring with an ultrametric norm; the cases of the blueprint are a finite
extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers `𝒪_E`, whose constant sheaf
`𝒪̂_{E,Y} : U ↦ C(U, 𝒪_E)` is the completed coefficient sheaf of Bhatt–Scholze. Let
`a : Y ⟶ s` be a morphism of schemes, in the blueprint the structure morphism of a separated
scheme of finite type over `s = Spec k`, `k` algebraically closed.
Following blueprint `def-weil-ordinary-compact-cohomology`, the coefficient complexes of
`K ∈ D(Y_proét, Λ)` are

`RΓ(Y, K) = Fib_s(Ra_* K)`, `RΓ_c(Y, K) = Fib_s(Ra_! K)`,

and `Hⁱ(Y, K)`, `Hⁱ_c(Y, K)` are their cohomology groups. Here `Ra_*` is the total right derived
functor of the pushforward of `Λ_Y`-modules, `Ra_! = Rḡ_* ∘ ī_!` for a compactification
`Y ⟶[ī] Z ⟶[ḡ] s` of `a` (an open immersion followed by a proper morphism), and `Fib_s`, the
evaluation at the geometric point of `s`, is the right derived functor of the sections over the
final object of the pro-étale site of `s`
(`AlgebraicGeometry.ProEtale.fieldGlobalSections`), with values in the derived category of
`Λ`-vector spaces.

For a constructible `Λ`-Weil sheaf or an object of `D^b_{c,W}(X, Λ)` on a `k₀`-scheme `X`, these
are applied to the underlying complex `For(K)` on the geometric fiber `X̄`
(`AlgebraicGeometry.FieldWeilComplex.cohomology`,
`AlgebraicGeometry.FieldWeilComplex.compactlySupportedCohomology`).

The coefficient object `Λ_Y` is the constant sheaf, with its canonical Weil structure
(`AlgebraicGeometry.FieldWeilSheaf.constant`), and for `Λ = E ⊆ ℚ̄_ℓ` its Tate twist `E_Y(m)`
(`AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant`) is the constant sheaf whose Weil
structure is multiplied by `χ_ℓ(σ)ᵐ`, `χ_ℓ` the `ℓ`-adic cyclotomic character and `σ` the
geometric Frobenius of `k̄`: as for `ℚ̄_ℓ` (`WeilConjectures.WeilSheaf.TateTwist`), the Tate
sheaf `E(1) = ℤ_ℓ(1) ⊗ E` is constant on the geometric fiber, with the geometric Frobenius acting
on `ℤ_ℓ(1)(k̄)` by `χ_ℓ(σ) = q⁻¹`. Then `Hⁱ(Y, E(m)) = Hⁱ(Y, For(E_Y(m)))`, and similarly with
compact support.

The finite stage `A_{E,n}` is `AlgebraicGeometry.Etale.cohomology` and
`AlgebraicGeometry.Etale.compactlySupportedCohomology`, the stage `ℚ̄_ℓ` is
`AlgebraicGeometry.WeilComplex.cohomology` and
`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`.

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldRightDerivedGlobalSections`,
  `AlgebraicGeometry.ProEtale.fieldCohomology`: `RΓ(Y, -)` and `Hⁱ(Y, -)`.
- `AlgebraicGeometry.ProEtale.fieldCompactlySupportedGlobalSections`,
  `AlgebraicGeometry.ProEtale.fieldCompactlySupportedCohomology`: `RΓ_c(Y, -)` and `Hⁱ_c(Y, -)`.
- `AlgebraicGeometry.FieldWeilSheaf.constant`, `AlgebraicGeometry.FieldWeilSheaf.constantTwist`,
  `AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant`: `Λ_Y`, constant twists, `E_Y(m)`.
- `AlgebraicGeometry.FieldWeilComplex.cohomology`,
  `AlgebraicGeometry.FieldWeilComplex.compactlySupportedCohomology`: the cohomology of Weil
  complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Endofunctor

namespace AlgebraicGeometry

namespace ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

namespace FieldSheaf

variable {Λ}

end FieldSheaf

variable {Λ} {Y s : Scheme.{u}} (a : Y ⟶ s)

section Integral

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))

end Integral

end ProEtale

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace FieldWeilSheaf

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))

end FieldWeilSheaf

namespace FieldWeilComplex

variable [HasCompactification (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure]

end FieldWeilComplex

namespace FieldWeilSheaf

variable [HasCompactification (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure]

end FieldWeilSheaf

end AlgebraicGeometry
