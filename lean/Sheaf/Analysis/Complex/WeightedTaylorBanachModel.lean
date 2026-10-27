module

public import Sheaf.Analysis.Complex.WeightedTaylorCoefficients
public import Sheaf.Analysis.Complex.AnalyticGerm
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # The weighted Taylor Banach algebra model

Source: Frenkel, Séminaire H. Cartan 1951–52, exposé 10, §§4–5, pp. 6–9;
the complete weighted coefficient model is agent supplied
(blueprint: lem-sfb-weighted-taylor-banach-model).
-/

@[expose] public section

set_option autoImplicit false

open Topology

namespace Complex.Taylor

/-- The conclusion of the weighted Taylor model, packaged to keep the canonical ring,
algebra, norm and map structures together. All underlying objects and operations are
fixed by the coefficient and representative equalities, not chosen arbitrarily.
Source: Frenkel, exposé 10, §§4–5; agent-supplied complete coefficient formulation
(blueprint: lem-sfb-weighted-taylor-banach-model). -/
class BanachModel where
  /-- Complete normed convolution algebras on the specified coefficient subtypes. -/
  coefficientRing : ∀ (d : ℕ) (ρ : Polyradius d), NormedCommRing (CoefficientSpace ρ)
  /-- Complex scalar multiplication is part of the normed algebra structure. -/
  coefficientAlgebra : ∀ (d : ℕ) (ρ : Polyradius d),
    @NormedAlgebra ℂ (CoefficientSpace ρ) _ (coefficientRing d ρ).toSeminormedRing
  /-- Completeness is for the uniformity of the specified norm. -/
  complete : ∀ (d : ℕ) (ρ : Polyradius d),
    @CompleteSpace (CoefficientSpace ρ)
      (coefficientRing d ρ).toNormedRing.toMetricSpace.toUniformSpace
  /-- The algebra of analytic germs. -/
  germRing : ∀ d : ℕ, CommRing (AnalyticGerm d)
  /-- Complex constants act on analytic germs. -/
  germAlgebra : ∀ d : ℕ, @Algebra ℂ (AnalyticGerm d) _ (germRing d).toSemiring

attribute [instance_reducible, instance] BanachModel.coefficientRing
attribute [instance_reducible, instance] BanachModel.coefficientAlgebra
attribute [instance_reducible, instance] BanachModel.germRing
attribute [instance_reducible, instance] BanachModel.germAlgebra

/-- All specified operations and comparison clauses for a packaged algebra model.
Source: Frenkel, exposé 10, §§4–5; agent-supplied complete coefficient formulation
(blueprint: lem-sfb-weighted-taylor-banach-model). -/
structure BanachModel.Spec [M : BanachModel] : Prop where
  /-- The coefficient inclusion fixes addition, multiplication, unit and complex scalars. -/
  coefficient_operations : ∀ (d : ℕ) (ρ : Polyradius d),
    ∃ ι : CoefficientSpace ρ →ₐ[ℂ] MvPowerSeries (Fin d) ℂ, ∀ c, ι c = c.val
  /-- The ring norm is the weighted absolute coefficient sum. -/
  norm_eq : ∀ (d : ℕ) (ρ : Polyradius d) (c : CoefficientSpace ρ),
    ‖c‖ = coefficientNorm ρ c
  /-- Germ ring operations are pointwise operations on representatives. -/
  germ_operations : ∀ d : ℕ,
    ∃ ι : AnalyticGerm d →+* Filter.Germ (𝓝 (0 : Fin d → ℂ)) ℂ, ∀ g, ι g = g.val
  /-- Complex scalar multiplication on germs is also pointwise. -/
  germ_scalar : ∀ (d : ℕ) (a : ℂ) (g : AnalyticGerm d), (a • g).val = a • g.val
  /-- Absolute convergence and local power-series analyticity on the entire open polydisc. -/
  convergence : ∀ (d : ℕ) (ρ : Polyradius d) (c : CoefficientSpace ρ),
    (∀ z ∈ polydisc ρ, Summable (fun α ↦ ‖c.val α * monomialValue α z‖)) ∧
      AnalyticOnNhd ℂ (seriesValue c) (polydisc ρ)
  /-- Each coefficient family gives its prescribed injective algebra map into germs. -/
  gamma : ∃ γ : ∀ (d : ℕ) (ρ : Polyradius d), CoefficientSpace ρ →ₐ[ℂ] AnalyticGerm d,
    (∀ (d : ℕ) (ρ : Polyradius d) (c : CoefficientSpace ρ),
      (γ d ρ c).val = Filter.Germ.ofFun (seriesValue c)) ∧
    (∀ (d : ℕ) (ρ : Polyradius d), Function.Injective (γ d ρ)) ∧
    (∀ (d : ℕ) (g : AnalyticGerm d), ∃ (ρ : Polyradius d) (c : CoefficientSpace ρ),
      γ d ρ c = g) ∧
    (∀ (d : ℕ) (ρ σ : Polyradius d), (∀ i, σ.val i ≤ ρ.val i) →
      ∃ r : CoefficientSpace ρ →ₐ[ℂ] CoefficientSpace σ,
        (∀ c, (r c).val = c.val) ∧
        (∀ c, ‖r c‖ ≤ ‖c‖) ∧ (∀ c, γ d σ (r c) = γ d ρ c)) ∧
    (∀ (d k : ℕ) (e : Fin k ↪ Fin d) (ρ : Polyradius d),
      ∃ r : CoefficientSpace ρ →ₐ[ℂ] CoefficientSpace (coordinateRadius e ρ),
        (∀ c α, (r c).val α = c.val (α.embDomain e)) ∧
        (∀ (c : CoefficientSpace ρ) (f : (Fin d → ℂ) → ℂ),
          Filter.Germ.ofFun f = (γ d ρ c).val →
          Filter.Germ.ofFun (f ∘ coordinateInclusion e) =
            (γ k (coordinateRadius e ρ) (r c)).val)) ∧
    (∀ ρ : Polyradius 0,
      ∃ (a : CoefficientSpace ρ ≃ₐ[ℂ] ℂ) (g : AnalyticGerm 0 ≃ₐ[ℂ] ℂ),
        (∀ c, a c = c.val 0) ∧
        (∀ h, h.val = Filter.Germ.ofFun (fun _ : Fin 0 → ℂ ↦ g h)) ∧
        (∀ c, g (γ 0 ρ c) = a c))

/-- Every positive polyradius gives the complete weighted Taylor algebra, with all germ,
radius and coordinate comparisons, including dimension zero.

Source: Frenkel, exposé 10, §§4–5, pp. 6–9. The complete model formulation is
agent supplied (blueprint: lem-sfb-weighted-taylor-banach-model).

Proof plan (the twelve steps of the DAG node):
1. In dimension zero the multiindex set is a singleton; its weight is one, and germs
   on the one-point space are constants.
2. Multiply each coefficient by its positive weight. This is a complex-linear
   isometry onto complex l1, so lem-sfb-complex-l1-completeness gives completeness.
3. The weight of a sum of multiindices is the product of their weights. Apply
   lem-sfb-absolute-series-product and lem-wf-summable-family-regrouping to the
   nonnegative product majorant, and lem-sfb-absolute-series-domination to convolution.
4. Finite coefficient sums give associativity, commutativity, distributivity and
   the unit supported at zero. The majorant gives the normed algebra inequality.
5. Dominate each evaluated monomial by its weighted coefficient majorant to obtain
   absolute convergence, using lem-sfb-absolute-series-domination.
6. At an interior point a choose positive t with |a|+t smaller than the radius.
   The coordinate binomial formula bounds finite subsums of the translated majorant
   by the original norm. Apply lem-sfb-absolute-series-domination.
7. Regroup this summable binomial family by the new multiindex, using
   lem-wf-summable-family-regrouping. Its sum is the translated power series,
   giving local analyticity at every interior point.
8. Addition, scalars and constants pass to germs. Products follow from
   lem-sfb-absolute-series-product and lem-wf-summable-family-regrouping;
   lem-sfb-complex-analytic-function-operations supplies analytic germ operations.
9. Equal germs have equal iterated coordinate derivatives at zero. Apply
   lem-sfb-monomial-series-coordinate-derivatives and cancel the nonzero multiindex
   factorial to obtain equality of every coefficient.
10. Every analytic germ has an absolutely convergent series on a sufficiently small
    positive closed polydisc. Its coefficients therefore belong to that weighted space.
11. Decreasing radii decreases every nonnegative coefficient weight; domination gives
    the norm inequality. The series agree on the smaller polydisc, hence as germs.
12. Setting coordinates to zero kills exactly the monomials with positive omitted
    exponents. The retained family is a summable subfamily by
    lem-wf-summable-family-regrouping, and gives the restricted germ. -/
theorem weightedTaylorBanachModel : ∃ M : BanachModel, @BanachModel.Spec M := by
  sorry

end Complex.Taylor
