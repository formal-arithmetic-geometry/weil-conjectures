/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.EulerProduct
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing

/-!
# Coefficient change, adic realization and the non-finite stages

The finite-coefficient trace formula is transported to the `ℓ`-adic stages
`Λ ∈ {𝒪_E, E, ℚ̄_ℓ}` in three steps: compact cohomology and geometric stalks commute with
a change of finite coefficient rings, a normalized uniform system of finite-level
complexes has a derived-complete realization over `𝒪_E` compatible with those two
operations, and the trace identity therefore passes to the limit and to the two field
stages, where it takes the shape of an Euler product.

Derived scalar extension `- ⊗ᴸ_A B` is not constructed in this project, so it enters the
first statement as a parameter `Ψ` subject to the compatibilities that its construction
would supply. The derived-completeness API of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.*` is used verbatim for the
second, which therefore fixes the coefficient category to `ModuleCat 𝒪_E`. The Euler
product of the third is stated for a finite-dimensional realization of the stalks and of
compactly supported cohomology, taken as a hypothesis, since the categorical trace of the
abstract coefficient stage is not a determinant.

## Main results

- `AlgebraicGeometry.ProEtale.nonempty_iso_comp_lowerShriek_and_upperStar` (blueprint
  `sk-p-trace-coeff`)
- `AlgebraicGeometry.ProEtale.derivedComplete_limit_and_nonempty_iso_limit` (blueprint
  `sk-prop-trace-adic`)
- `AlgebraicGeometry.ProEtale.trace_globalOperator_eq_sum_and_eulerProduct` (blueprint
  `sk-thm-trace-transport`)
-/

@[expose] public section

universe w u'' u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {B : Type u''} [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] {s X : Scheme.{u}}

/-- Blueprint `sk-p-trace-coeff`: Finite-level coefficient change.

For a homomorphism `A ⟶ B` of finite coefficient rings, derived scalar extension
`- ⊗ᴸ_A B` commutes with the six operations, and applying this to `Ra_{X!}` and to a
geometric stalk gives

`(Ra_{X!} K) ⊗ᴸ B ≅ Ra_{X!} (K ⊗ᴸ B)` and `(K ⊗ᴸ B)_x̄ ≅ K_x̄ ⊗ᴸ B`.

Derived scalar extension along a map of coefficient *rings* does not exist in this
project: coefficients are abstract monoidal Grothendieck abelian categories, and the
functor `- ⊗ᴸ_A B` between the associated derived categories of pro-étale sheaves is part
of the six-operations chapter. It is therefore a parameter `Ψ` of the statement, a family
of functors `Ψ Z : D(Z, A) ⥤ D(Z, B)` indexed by the schemes, and the compatibilities that
its construction supplies are hypotheses: `Ψ` commutes with `Lg^*`, and with `Rg_*` for an
open immersion and for a proper `g`. These are exactly the ingredients out of which
`Rf_! = Rf̄_* ∘ j_!` is assembled, which is why the conclusion for `Rf_!` is the content of
the proposition.

Both conclusions are `Nonempty` isomorphisms of *functors*, since the comparison maps
themselves are not available. Naturality is what the sketch's "the comparisons are
natural, hence compatible with the Frobenius maps" means: a natural isomorphism
automatically intertwines `Ψ` applied to a Frobenius coefficient morphism `φ` with the
Frobenius coefficient morphism of the image Weil complex, so no Weil structure has to
appear in the statement. The second conclusion is the pullback hypothesis read at the
geometric point `x̄`; it is recorded because it is one of the two displayed
compatibilities of the sketch and is what the transport argument cites. -/
theorem nonempty_iso_comp_lowerShriek_and_upperStar
    (Ψ : ∀ Z : Scheme.{u}, DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) B))
    (_hupperStar : ∀ {Z Z' : Scheme.{u}} (g : Z ⟶ Z'),
      Nonempty ((upperStar A g).leftDerivedFunctor ⋙ Ψ Z ≅
        Ψ Z' ⋙ (upperStar B g).leftDerivedFunctor))
    (_hlowerStarOpen : ∀ {Z Z' : Scheme.{u}} (g : Z ⟶ Z'), IsOpenImmersion g →
      Nonempty ((lowerStar A g).rightDerivedFunctor ⋙ Ψ Z' ≅
        Ψ Z ⋙ (lowerStar B g).rightDerivedFunctor))
    (_hlowerStarProper : ∀ {Z Z' : Scheme.{u}} (g : Z ⟶ Z'), IsProper g →
      Nonempty ((lowerStar A g).rightDerivedFunctor ⋙ Ψ Z' ≅
        Ψ Z ⋙ (lowerStar B g).rightDerivedFunctor))
    (aX : X ⟶ s) [HasCompactification aX] (x : s ⟶ X) :
    Nonempty (rightDerivedLowerShriek A aX ⋙ Ψ s ≅ Ψ X ⋙ rightDerivedLowerShriek B aX) ∧
      Nonempty ((upperStar A x).leftDerivedFunctor ⋙ Ψ s ≅
        Ψ X ⋙ (upperStar B x).leftDerivedFunctor) :=
  sorry

/-- Blueprint `sk-prop-trace-adic`: Adic realization.

A system `K_• = (K_n, t_{n+1,n})` of finite-level complexes is *normalized* if
`K_n ⊗ᴸ_{A_n} A_j ≅ K_j` for `j ≤ n`, and *uniform* if the `K_n` share a cohomological
range and Tor amplitude. Clause **(i)** says that the realization
`K_{𝒪_E} = R lim_n K_n` of such a system is derived complete and satisfies
`K_{𝒪_E} ⊗ᴸ_{𝒪_E} A_n ≅ K_n`; clause **(ii)** says that `RΓ_c(X, -)` and the geometric
stalk at a point `x̄ : s ⟶ X` commute with realization and that the two realizations are
perfect.

The rendering follows the project's derived-completeness API, which models the whole
tower inside the single derived category `D(X, 𝒪_E)` of sheaves of `𝒪_E`-modules rather
than in a sequence of categories `D(X, A_n)`: `A_n` is `R ⧸ Iⁿ` for a ring `R` with an
ideal `I` (the intended case being `R = 𝒪_E`, `I = 𝔪_E`, so that `R` is `I`-adically
complete), the reduction `K ⊗ᴸ A_n` is `DerivedCategory.derivedCompletionDiagram` evaluated
at `n`, derived completeness is `DerivedCategory.derivedComplete`, and `R lim` is
`CategoryTheory.Limits.limit`. This forces the coefficient category to be
`ModuleCat 𝒪_E`, which does satisfy the standard coefficient instance block, so that the
pro-étale operations `Rf_!` and `Lx̄^*` apply to it unchanged. Perfectness is
`HasRightDual`, and since it is data it is concluded as `Nonempty (HasRightDual …)`.

Two parts of the sketch are not rendered. The cohomological range and the Tor amplitude
have no counterpart in the present API, so "lies in the same range" and the uniformity
hypothesis are omitted; the perfectness conclusions of clause (ii) are the part of that
bookkeeping which is expressible. Equivariance of the isomorphisms of clause (ii) for the
global and local Frobenius operators cannot be stated, because the isomorphisms are only
asserted to exist.

Clause **(iii)**, rationalization and coefficient-field extension, is omitted here because
it is already carried by the project: `CategoryTheory.Rationalization` is *defined* as the
localization of a triangulated category at the torsion morphisms,
`DerivedCategoryDerivedCompleteRational` is by definition the rationalization of
`DerivedCategoryDerivedCompleteIntegral` at the nonzero divisors of `𝒪_E`, it is
triangulated and `E`-linear by the instances proved there, and
`DerivedCategoryDerivedCompleteRational.fromIntegral` is the canonical functor, which is
the identity on objects. What those files do not yet record — idempotent completeness and
the resulting equivalence with the Karoubi envelope, the presentation of every rational
morphism as `ϖ^{-N} u`, and the description of the `ℚ̄_ℓ`-stage as a filtered colimit over
finite `E/ℚ_ℓ` — is left to that development rather than restated here. -/
theorem derivedComplete_limit_and_nonempty_iso_limit {R : Type (u + 1)} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (aX : X ⟶ s) [HasCompactification aX] (x : s ⟶ X)
    (K : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (_hnorm : ∀ n j : ℕ, j ≤ n →
      Nonempty ((DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I
        (K.obj (Opposite.op n))).obj (Opposite.op j) ≅ K.obj (Opposite.op j)))
    [HasLimit K] [HasLimit (K ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX)]
    [HasLimit (K ⋙ (upperStar (ModuleCat.{u + 1} R) x).leftDerivedFunctor)]
    [∀ n, HasRightDual ((K ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX).obj n)]
    [∀ n, HasRightDual
      ((K ⋙ (upperStar (ModuleCat.{u + 1} R) x).leftDerivedFunctor).obj n)] :
    DerivedCategory.derivedComplete (Scheme.ProEt.topology X) I (limit K) ∧
      (∀ n : ℕ, Nonempty
        ((DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I
          (limit K)).obj (Opposite.op n) ≅ K.obj (Opposite.op n))) ∧
      Nonempty ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX).obj (limit K) ≅
        limit (K ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX)) ∧
      Nonempty (((upperStar (ModuleCat.{u + 1} R) x).leftDerivedFunctor).obj (limit K) ≅
        limit (K ⋙ (upperStar (ModuleCat.{u + 1} R) x).leftDerivedFunctor)) ∧
      Nonempty (HasRightDual
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX).obj (limit K))) ∧
      Nonempty (HasRightDual
        (((upperStar (ModuleCat.{u + 1} R) x).leftDerivedFunctor).obj (limit K))) :=
  sorry

open scoped PowerSeries.WithPiTopology in
/-- Blueprint `sk-thm-trace-transport`: Transport of the trace formula to the non-finite stages.

Let `Λ` be one of the three non-finite coefficient stages: the `𝒪_E`-stage, whose objects
are the normalized systems of finite-level objects realized by
`derivedComplete_limit_and_nonempty_iso_limit`, its rationalization `E`, or the colimit
`ℚ̄_ℓ` over finite `E/ℚ_ℓ`. Clause **(a)** is that the finite-level trace formula

`tr_Λ(F_{c,m} ∣ RΓ_c(X, K)) = ∑_{x ∈ X₀(𝐅_{q^m})} tr_Λ(F_{x,m} ∣ K_x̄)`

continues to hold at each of them, and clause **(b)** is its Euler-product form

`L(X₀, K, T) = ∏_x det(1 - T^{e_x} F_x ∣ K_x̄)^{-1}`, equal to
`∏_i det(1 - T F ∣ H_c^i(X, K))^{(-1)^{i+1}}`,

in `1 + T Λ[[T]]`, for `Λ ∈ {E, ℚ̄_ℓ}`.

Clause (a) is rendered exactly as `trace_globalOperator_eq_sum_trace_stalkFrobenius` is,
for a general coefficient category `A`; the three stages are the intended instantiations
of `A` and are recorded here rather than in the type, since the project has no construction
of the three coefficient categories as monoidal Grothendieck abelian categories. Rational
points are the `s`-points of `X` fixed by `Φ_m`, `tr` is
`CategoryTheory.MonoidalCategory.trace`, which needs the braiding of `D(s, A)` as an
instance hypothesis, and the finiteness of the fixed points and the perfectness of the
compactly supported cohomology and of the stalks are hypotheses.

Clause (b) is not a statement about the abstract coefficient category: a determinant needs
an actual finite-dimensional vector space. It is therefore stated for a realization taken
as a hypothesis — a ring map `θ` from the coefficient ring `End (𝟙_ D(s, A))` of the stage
to a field `Λ` of characteristic zero, finite-dimensional `Λ`-vector spaces `Hc i` and
`St y i` with endomorphisms realizing `H_c^i(X, K)` and the cohomology of the stalk
`K_ȳ` at a closed point `y` of `X₀` in degrees `i ∈ degs`, and the two hypotheses
`_hHc`, `_hSt` saying that `θ` carries the categorical traces of clause (a) to the
alternating linear-algebra traces, the point side being regrouped as in the sketch: a
closed point `y` of degree `e_y` contributes `e_y` rational points, each with stalk
Frobenius `F_y^{m/e_y}`, exactly when `e_y ∣ m`. The determinant
`det(1 - T^{e_y} F_y ∣ K_ȳ)` of a complex is the alternating product over `degs` of the
reciprocal characteristic polynomials `LinearMap.charpolyRev` with `T` substituted by
`T^{e_y}`, and `∏_x` is the coefficientwise infinite product `tprod` of
`AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod`, whose local finiteness is part of the
assertion; the coefficient field carries the discrete topology, so that `tprod` in
`PowerSeries Λ` is exactly the coefficientwise, locally finite product. The passage from
(a) to (b) is `LinearMap.inv_charpolyRev_eq_exp`. The
compatibility of the identity with an embedding `ι : ℚ̄_ℓ ⟶ ℂ` is not stated separately:
it is the image of the identity under the ring map `PowerSeries.map ι`. -/
theorem trace_globalOperator_eq_sum_and_eulerProduct (G : GeometricOperations A s)
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    {aX : X ⟶ s} [HasCompactification aX] (W : WeilComplex (A := A) aX) (_hW : IsIso W.coeff)
    (_hctf : G.ctf X W.obj)
    [∀ m : ℕ, IsProper (W.graph m).snd] [∀ m : ℕ, HasCompactification (W.graph m).snd]
    [∀ m : ℕ, Fintype {x : s ⟶ X // x ≫ W.frobeniusIterate m = x}]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [∀ x : s ⟶ X, HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k))
    [QuasiCompact f₀] [LocallyOfFiniteType f₀]
    {Λ : Type w} [Field Λ] [CharZero Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (degs : Finset ℤ)
    {Hc : ℤ → Type w} [∀ i, AddCommGroup (Hc i)] [∀ i, Module Λ (Hc i)]
    [∀ i, FiniteDimensional Λ (Hc i)] (Fc : ∀ i, Module.End Λ (Hc i))
    {St : X₀ → ℤ → Type w} [∀ y i, AddCommGroup (St y i)] [∀ y i, Module Λ (St y i)]
    [∀ y i, FiniteDimensional Λ (St y i)] (Fst : ∀ y i, Module.End Λ (St y i))
    (θ : End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) →+* Λ)
    (_hHc : ∀ m : ℕ, 1 ≤ m →
      θ (MonoidalCategory.trace (Correspondence.globalOperator G (W.graph m))) =
        ∑ i ∈ degs, (i.negOnePow : ℤ) • LinearMap.trace Λ (Hc i) (Fc i ^ m))
    (_hSt : ∀ m : ℕ, 1 ≤ m →
      ∑ y : {x : s ⟶ X // x ≫ W.frobeniusIterate m = x},
          θ (MonoidalCategory.trace (W.stalkFrobenius m y.1 y.2)) =
        ∑ᶠ y : X₀.finitePoints, if f₀.degreeOver y.1 ∣ m then (f₀.degreeOver y.1 : Λ) *
          ∑ i ∈ degs, (i.negOnePow : ℤ) •
            LinearMap.trace Λ (St y.1 i) (Fst y.1 i ^ (m / f₀.degreeOver y.1)) else 0) :
    (∀ m : ℕ, 1 ≤ m →
        MonoidalCategory.trace (Correspondence.globalOperator G (W.graph m)) =
          ∑ y : {x : s ⟶ X // x ≫ W.frobeniusIterate m = x},
            MonoidalCategory.trace (W.stalkFrobenius m y.1 y.2)) ∧
      ∏' y : X₀.finitePoints, (∏ i ∈ degs, if Even i then
          ((Fst y.1 i).charpolyRev.comp (Polynomial.X ^ f₀.degreeOver y.1) : PowerSeries Λ)
        else ((Fst y.1 i).charpolyRev.comp (Polynomial.X ^ f₀.degreeOver y.1) :
          PowerSeries Λ)⁻¹)⁻¹ =
        ∏ i ∈ degs, if Even i then ((Fc i).charpolyRev : PowerSeries Λ)⁻¹
          else ((Fc i).charpolyRev : PowerSeries Λ) :=
  sorry

end AlgebraicGeometry.ProEtale
