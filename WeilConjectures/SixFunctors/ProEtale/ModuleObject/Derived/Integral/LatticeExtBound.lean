/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!
# An `Ext` bound between extensions by zero of lattices

Let `E` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, `X` a noetherian scheme on
which `ℓ` is invertible, `i : Z ⟶ X` a closed immersion with open complement `j : V ⟶ X`,
`u : S ⟶ Z` an open immersion, `a = i ∘ u`, and `L₀` a locally free `𝒪_{E,S}`-module of finite
rank. For every locally closed immersion `b = i' ∘ u' : T ⟶ X` and every locally free
`𝒪_{E,T}`-module `M₀` of finite rank,

`Ext^q_{𝒪_E}(a_! L₀, b_! M₀) = 0` for `q > cd_ℓ(j) + cd_ℓ(S) + 2`

(`AlgebraicGeometry.ProEtale.CondensedRing.eq_zero_of_cohomologicalDimension_add_two_lt`).

## Implementation details

The locally closed immersion `b` is given by a factorisation `T ⟶ Z' ⟶ X` into an open immersion
followed by a closed immersion, and `b_! = i'_* u'_!`.

The proof is not formalised yet. It bounds the complex `RΓ(S, L₀^∨ ⊗ u^* RΓ_Z b_!(M₀/π^n))` in
degrees `≤ cd_ℓ(j) + cd_ℓ(S) + 1` (the torsion bound), and passes to the derived limit over `n`,
which commutes with the functors involved
(`AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_upperStar_tensor_isGE_and_isHomotopyLimit`)
and costs one degree. The integral `Ext` bound
`CategoryTheory.brownHypotheses_integral_uniformExtBound_of_finite_cd` follows the same route for
constructible targets, but allows torsion in `L₀` and in the target and only reaches the
bound `cd_ℓ(j) + cd_ℓ(S) + 3`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Let `i : Z ⟶ X` be a closed immersion of noetherian schemes with open complement
`j : V ⟶ X`, with `ℓ` invertible on `X`, let `u : S ⟶ Z` be an open immersion, `a = i ∘ u`, and
`L₀` a locally free `𝒪_{E,S}`-module of finite rank. For every locally closed immersion
`b = i' ∘ u' : T ⟶ X` and locally free `𝒪_{E,T}`-module `M₀` of finite rank,
`Ext^q_{𝒪_E}(a_! L₀, b_! M₀) = 0` for `q > cd_ℓ(j) + cd_ℓ(S) + 2`. -/
theorem eq_zero_of_cohomologicalDimension_add_two_lt
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Z V S Z' T : Scheme.{u}} [IsNoetherian X] (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (j : V ⟶ X) (u : S ⟶ Z) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] [IsOpenImmersion u] (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (i' : Z' ⟶ X) (u' : T ⟶ Z') [IsClosedImmersion i'] [IsOpenImmersion u'] :
    letI : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
    letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType u
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    ∀ (c s : ℕ), relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c →
      cohomologicalDimension l (Fact.out : l.Prime) S ≤ s →
    ∀ (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S)),
      LocallyFree (condensedRingObj A S) L₀ →
    ∀ (M₀ : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj A T)),
      LocallyFree (condensedRingObj A T) M₀ →
    ∀ (q : ℤ), (c : ℤ) + s + 2 < q →
    ∀ f : (DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar A i).obj ((openImmersionLowerShriek A u).obj L₀)) ⟶
      (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar A i').obj ((openImmersionLowerShriek A u').obj M₀))),
      f = 0 := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
