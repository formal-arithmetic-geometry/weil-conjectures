/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.EulerProduct
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main
public import WeilConjectures.ZetaLinearAlgebra.DetTrace

/-!
# Coefficient change, adic realization and the Euler product

The finite-coefficient trace formula is transported to the `ℓ`-adic stages
`Λ ∈ {𝒪_E, E, ℚ̄_ℓ}` in three steps: compact cohomology and geometric stalks commute with
a change of finite coefficient rings, a normalized system of finite-level complexes has a
derived-complete realization over `𝒪_E` compatible with those two operations, and the
trace identity therefore passes to the limit and to the two field stages, where it takes
the shape of an Euler product.

## Main results

- `AlgebraicGeometry.ProEtale.nonempty_rightDerivedLowerShriek_comp_iso`: compact
  cohomology commutes with a change of finite coefficients.
- `AlgebraicGeometry.ProEtale.derivedComplete_limit`,
  `AlgebraicGeometry.ProEtale.nonempty_derivedCompletionDiagram_obj_limit_iso`,
  `AlgebraicGeometry.ProEtale.nonempty_rightDerivedLowerShriek_obj_limit_iso`,
  `AlgebraicGeometry.ProEtale.nonempty_leftDerivedUpperStar_obj_limit_iso`: the adic
  realization of a normalized system and its compatibilities.
- `AlgebraicGeometry.ProEtale.hasProd_inv_alternatingCharpolyRevProd`: the Euler-product
  form of the trace formula.

## Implementation notes

Derived scalar extension along a map of coefficient *rings* does not exist in this
project: coefficients are abstract monoidal Grothendieck abelian categories, and the
functor `- ⊗ᴸ_A B` between the associated derived categories of pro-étale sheaves is part
of the six-operations chapter. It is therefore a parameter `Ψ` of the first statement,
a family of functors `Ψ Z : D(Z, A) ⥤ D(Z, B)`, and the compatibilities that its
construction supplies are hypotheses: `Ψ` commutes with `Lg^*`, and with `Rg_*` for an
open immersion and for a proper `g`. These are exactly the ingredients out of which
`Rf_! = Rf̄_* ∘ j_!` is assembled, which is why the conclusion for `Rf_!` is the content of
the proposition. The blueprint's second assertion, for a geometric stalk, is the pullback
hypothesis read at the point, so it gets no separate declaration. The conclusion is a
`Nonempty` isomorphism of *functors*, since the comparison maps themselves are not
available; naturality is what the sketch's "the comparisons are natural, hence compatible
with the Frobenius maps" means.

The adic realization follows the project's derived-completeness API, which models the whole
tower inside the single derived category `D(X, 𝒪_E)` of sheaves of `𝒪_E`-modules rather
than in a sequence of categories `D(X, A_n)`: `A_n` is `R ⧸ Iⁿ` for a ring `R` with an
ideal `I` (the intended case being `R = 𝒪_E`, `I = 𝔪_E`, so that `R` is `I`-adically
complete), the reduction `K ⊗ᴸ A_n` is `DerivedCategory.derivedCompletionDiagram` evaluated
at `n`, derived completeness is `DerivedCategory.derivedComplete`, and `R lim` is
`CategoryTheory.Limits.limit`. This forces the coefficient category to be
`ModuleCat 𝒪_E`, which does satisfy the standard coefficient instance block, so that the
pro-étale operations `Rf_!` and `Lx̄^*` apply to it unchanged.

Three parts of the sketch of the adic realization are not rendered. The cohomological range
and the Tor amplitude have no counterpart in the present API, so "lies in the same range"
and the uniformity hypothesis are omitted — and with them the perfectness conclusions,
which are exactly what uniformity buys. Equivariance of the isomorphisms for the global and
local Frobenius operators cannot be stated, because the isomorphisms are only asserted to
exist. Rationalization and coefficient-field extension are already carried by the project:
`CategoryTheory.Rationalization` is *defined* as the localization of a triangulated
category at the torsion morphisms, `DerivedCategoryDerivedCompleteRational` is by
definition the rationalization of `DerivedCategoryDerivedCompleteIntegral` at the nonzero
divisors of `𝒪_E`, and `DerivedCategoryDerivedCompleteRational.fromIntegral` is the
canonical functor.

The Euler product is not a statement about the abstract coefficient category: a determinant
needs an actual finite-dimensional vector space. It is therefore stated for a realization
taken as a hypothesis — a ring map `θ` from the coefficient ring `End (𝟙_ D(s, A))` of the
stage to a field `Λ` of characteristic zero, finite-dimensional `Λ`-vector spaces `Hc i`
and `St y i` with endomorphisms realizing `H_c^i(X, K)` and the cohomology of the stalk
`K_ȳ` at a closed point `y` of `X₀`, and the two hypotheses `hHc`, `hSt` saying that `θ`
carries the categorical traces of the global Frobenius and of the stalk Frobenius
`F_{x,m}` at each fixed point `x` lying over `y` to the alternating linear-algebra traces of
`F^m` and `F_y^{m/e_y}`. The regrouping of the point side — a closed point `y` of degree
`e_y` contributes `e_y` rational points exactly when `e_y ∣ m` — is part of the assertion.
The scheme `X₀` is tied to `X` by `hΦ`, which exhibits `X` as its base change along
`s ⟶ Spec k` and the Frobenius as the base change of that of `X₀`. The passage from the
trace identity to the product is `LinearMap.inv_charpolyRev_eq_exp`, and the coefficient
field carries the discrete topology, so that `HasProd` in `PowerSeries Λ` is exactly
coefficientwise local finiteness together with the value of the product. Compatibility
with an embedding `ι : ℚ̄_ℓ ⟶ ℂ` is not stated separately: it is the image of the identity
under `PowerSeries.map ι`.
-/

@[expose] public section

universe w u'' u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {B : Type u''} [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] {s X : Scheme.{u}}

/-- Finite-level coefficient change for compactly supported cohomology: derived scalar
extension `- ⊗ᴸ_A B` commutes with `Ra_{X!}`, that is, `(Ra_{X!} K) ⊗ᴸ B ≅ Ra_{X!}(K ⊗ᴸ B)`
(blueprint: `sk-p-trace-coeff`). -/
theorem nonempty_rightDerivedLowerShriek_comp_iso
    (Ψ : ∀ Z : Scheme.{u}, DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) B))
    (hupperStar : ∀ {Z Z' : Scheme.{u}} (g : Z ⟶ Z'),
      Nonempty ((upperStar A g).leftDerivedFunctor ⋙ Ψ Z ≅
        Ψ Z' ⋙ (upperStar B g).leftDerivedFunctor))
    (hlowerStarOpen : ∀ {Z Z' : Scheme.{u}} (g : Z ⟶ Z'), IsOpenImmersion g →
      Nonempty ((lowerStar A g).rightDerivedFunctor ⋙ Ψ Z' ≅
        Ψ Z ⋙ (lowerStar B g).rightDerivedFunctor))
    (hlowerStarProper : ∀ {Z Z' : Scheme.{u}} (g : Z ⟶ Z'), IsProper g →
      Nonempty ((lowerStar A g).rightDerivedFunctor ⋙ Ψ Z' ≅
        Ψ Z ⋙ (lowerStar B g).rightDerivedFunctor))
    (aX : X ⟶ s) [HasCompactification aX] :
    Nonempty (rightDerivedLowerShriek A aX ⋙ Ψ s ≅ Ψ X ⋙ rightDerivedLowerShriek B aX) :=
  sorry

/-- Adic realization, derived completeness: the realization `K_{𝒪_E} = R lim_n K_n` of a
normalized system `K_• = (K_n, t_{n+1,n})` of finite-level complexes is derived complete
(blueprint: `sk-prop-trace-adic`). -/
theorem derivedComplete_limit {R : Type (u + 1)} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R]
    (K : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (hnorm : ∀ n j : ℕ, j ≤ n →
      Nonempty ((DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I
        (K.obj (Opposite.op n))).obj (Opposite.op j) ≅ K.obj (Opposite.op j)))
    [HasLimit K] :
    DerivedCategory.derivedComplete (Scheme.ProEt.topology X) I (limit K) :=
  sorry

/-- Adic realization, levelwise reduction: the realization of a normalized system reduces
to the given levels, `K_{𝒪_E} ⊗ᴸ_{𝒪_E} A_n ≅ K_n`
(blueprint: `sk-prop-trace-adic`). -/
theorem nonempty_derivedCompletionDiagram_obj_limit_iso {R : Type (u + 1)} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (K : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (hnorm : ∀ n j : ℕ, j ≤ n →
      Nonempty ((DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I
        (K.obj (Opposite.op n))).obj (Opposite.op j) ≅ K.obj (Opposite.op j)))
    [HasLimit K] (n : ℕ) :
    Nonempty ((DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I
      (limit K)).obj (Opposite.op n) ≅ K.obj (Opposite.op n)) :=
  sorry

/-- Adic realization, compact cohomology: `RΓ_c(X, -)` commutes with realization
(blueprint: `sk-prop-trace-adic`). -/
theorem nonempty_rightDerivedLowerShriek_obj_limit_iso {R : Type (u + 1)} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (aX : X ⟶ s) [HasCompactification aX]
    (K : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (hnorm : ∀ n j : ℕ, j ≤ n →
      Nonempty ((DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I
        (K.obj (Opposite.op n))).obj (Opposite.op j) ≅ K.obj (Opposite.op j)))
    [HasLimit K] [HasLimit (K ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX)] :
    Nonempty ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX).obj (limit K) ≅
      limit (K ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX)) :=
  sorry

/-- Adic realization, geometric stalks: the stalk at a geometric point `x̄ : s ⟶ X`
commutes with realization (blueprint: `sk-prop-trace-adic`). -/
theorem nonempty_leftDerivedUpperStar_obj_limit_iso {R : Type (u + 1)} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (x : s ⟶ X)
    (K : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (hnorm : ∀ n j : ℕ, j ≤ n →
      Nonempty ((DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I
        (K.obj (Opposite.op n))).obj (Opposite.op j) ≅ K.obj (Opposite.op j)))
    [HasLimit K]
    [HasLimit (K ⋙ (upperStar (ModuleCat.{u + 1} R) x).leftDerivedFunctor)] :
    Nonempty (((upperStar (ModuleCat.{u + 1} R) x).leftDerivedFunctor).obj (limit K) ≅
      limit (K ⋙ (upperStar (ModuleCat.{u + 1} R) x).leftDerivedFunctor)) :=
  sorry

open scoped PowerSeries.WithPiTopology in
/-- **The Euler product form of the trace formula.** For a realization of the stalks and of
compactly supported cohomology over a field `Λ` of characteristic zero,

`L(X₀, K, T) = ∏_y det(1 - T^{e_y} F_y ∣ K_ȳ)^{-1}`, equal to
`∏_i det(1 - T F ∣ H_c^i(X, K))^{(-1)^{i+1}}`,

in `1 + T Λ[[T]]`, the product over the closed points `y` of `X₀` being coefficientwise
locally finite. This is the Euler-product form of
`trace_globalOperator_eq_sum_trace_stalkFrobenius`
(blueprint: `sk-thm-trace-transport`). -/
theorem hasProd_inv_alternatingCharpolyRevProd [DerivedBraiding A] {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (G : GeometricOperations A (Spec (.of Ω))) {aX : X ⟶ Spec (.of Ω)}
    [HasCompactification aX] (W : WeilComplex (A := A) aX) (hW : IsIso W.coeff)
    (hctf : G.ctf X W.obj)
    [∀ m : ℕ, IsProper (W.graph G m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [∀ x : Spec (.of Ω) ⟶ X, HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k))
    [IsSeparated f₀] [QuasiCompact f₀] [LocallyOfFiniteType f₀] (σ : Spec (.of Ω) ⟶ Spec (.of k))
    (p : X ⟶ X₀) (hΦ : W.IsModelFrobenius f₀ σ p)
    {Λ : Type w} [Field Λ] [CharZero Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (degs : Finset ℤ)
    {Hc : ℤ → Type w} [∀ i, AddCommGroup (Hc i)] [∀ i, Module Λ (Hc i)]
    [∀ i, FiniteDimensional Λ (Hc i)] (Fc : ∀ i, Module.End Λ (Hc i))
    {St : X₀ → ℤ → Type w} [∀ y i, AddCommGroup (St y i)] [∀ y i, Module Λ (St y i)]
    [∀ y i, FiniteDimensional Λ (St y i)] (Fst : ∀ y i, Module.End Λ (St y i))
    (θ : End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) A))) →+* Λ)
    (hHc : ∀ m : ℕ, 1 ≤ m →
      θ (MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G m))) =
        ∑ i ∈ degs, (i.negOnePow : ℤ) • LinearMap.trace Λ (Hc i) (Fc i ^ m))
    (hSt : ∀ m : ℕ, 1 ≤ m →
      ∀ x : {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x},
      ∀ y : X₀.finitePoints, y.1 ∈ Set.range (x.1 ≫ p).base →
        θ (MonoidalCategory.trace (W.stalkFrobenius m x.1 x.2.2)) =
          ∑ i ∈ degs, (i.negOnePow : ℤ) •
            LinearMap.trace Λ (St y.1 i) (Fst y.1 i ^ (m / f₀.degreeOver y.1))) :
    HasProd
      (fun y : X₀.finitePoints ↦
        (LinearMap.alternatingCharpolyRevProd degs (Fst y.1) (f₀.degreeOver y.1))⁻¹)
      (LinearMap.alternatingCharpolyRevProd degs Fc 1)⁻¹ :=
  sorry

end AlgebraicGeometry.ProEtale
