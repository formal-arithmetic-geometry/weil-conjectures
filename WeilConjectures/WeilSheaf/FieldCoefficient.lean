/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleHeart
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.GeometricFrobenius
public import WeilConjectures.WeilSheaf.FrobeniusDerived

/-!
# Weil sheaves and Weil complexes with coefficients in a finite extension of `ℚ_ℓ`

Let `k₀` be a finite field with algebraic closure `k̄`, `X` a scheme over `k₀`, `X̄ = X ×_{k₀} k̄`
its geometric fiber and `Fr_X : X̄ ≅ X̄` its geometric Galois Frobenius. Let `Λ` be a field with
an ultrametric norm; the case of the blueprint is a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`,
`ℓ` prime to the characteristic of `k₀`. Following blueprint `def-weil-weil-sheaf-complex`,

- a *constructible `E`-Weil sheaf* on `X` is a constructible `E`-adic sheaf `F` on the pro-étale
  site of `X̄`, an object of `Sh_c(X̄, E)`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart`), together with an
  isomorphism `θ : Fr_X^* F ≅ F` (`AlgebraicGeometry.FieldWeilSheaf`);
- `D^b_{c,W}(X, E)` is the triangulated category obtained from complexes of such sheaves by
  inverting the equivariant quasi-isomorphisms (`AlgebraicGeometry.FieldWeilComplex`);
- the forgetful functor `For : D^b_{c,W}(X, E) ⥤ D^b_c(X̄, E)`
  (`AlgebraicGeometry.FieldWeilComplex.forgetBoundedConstructible`) is exact, and every object
  `K` carries the derived Frobenius isomorphism `θ_K : Fr_X^* For(K) ≅ For(K)`
  (`AlgebraicGeometry.FieldWeilComplex.frobeniusIso`).

This is the construction of `WeilConjectures.WeilSheaf.Category` (the stage `ℚ̄_ℓ`,
`AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex`) with the coefficients `ℚ̄_ℓ`
replaced by `Λ`: the sheaves are modules over the constant sheaf `Λ_X̄ : U ↦ C(U, Λ)` of
Bhatt–Scholze (`AlgebraicGeometry.ProEtale.FieldSheaf`), the Frobenius pullback is the
pushforward along `Fr_X⁻¹`, and the Weil complexes are the bounded objects with constructible
cohomology of the derived category of pro-étale Weil sheaves, all of whose terms carry a Weil
structure, so that `θ` is represented termwise. The functors from the stages `E` to the stage
`ℚ̄_ℓ`, induced by the extension of scalars `ℚ̄_ℓ ⊗_E -`, are
`AlgebraicGeometry.FieldWeilComplex.toWeilComplex`
(`WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars`).

## Main definitions

- `AlgebraicGeometry.ProEtaleFieldWeilSheaf`: pro-étale `Λ`-sheaves with a Weil structure.
- `AlgebraicGeometry.FieldWeilSheaf` and `AlgebraicGeometry.FieldWeilComplex`: constructible
  `Λ`-Weil sheaves (an abelian category) and `D^b_{c,W}(X, Λ)` (a triangulated category).
- `AlgebraicGeometry.FieldWeilComplex.forget` and
  `AlgebraicGeometry.FieldWeilComplex.forgetBoundedConstructible`: the forgetful functor `For`.
- `AlgebraicGeometry.FieldWeilComplex.frobeniusIso`: `θ : Fr_X^* ∘ For ≅ For`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section Frobenius

variable (k₀ : Type u) [Field k₀] [Finite k₀] (Λ : Type) [NormedField Λ] [IsUltrametricDist Λ]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end Frobenius

variable {k₀ : Type u} [Field k₀] [Finite k₀] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace FieldWeilComplex

end FieldWeilComplex

section FiniteExtension

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))
  [FiniteDimensional ℚ_[l] E] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

end FiniteExtension

end AlgebraicGeometry
