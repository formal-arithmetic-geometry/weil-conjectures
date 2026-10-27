module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.Localization.Defs

/-!
# Axes and total fractions of the formal split node

Source: Stacks Project, Tag 0C4A, proof of lemma-2-branches-delta-1, Case I, q = xy.
(blueprint: lem-trf-formal-node-axes-total-fractions)
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

namespace MvPowerSeries

/-- The ideal (uv) in k[[u,v]]. Source: Stacks Project, Tag 0C4A, Case I.
(blueprint: lem-trf-formal-node-axes-total-fractions) -/
def formalNodeIdeal (k : Type u) [Field k] : Ideal (MvPowerSeries (Fin 2) k) :=
  Ideal.span {X (0 : Fin 2) * X (1 : Fin 2)}

/-- The formal split node k[[u,v]]/(uv). Source: Stacks Project, Tag 0C4A, Case I.
(blueprint: lem-trf-formal-node-axes-total-fractions) -/
abbrev FormalNodeRing (k : Type u) [Field k] :=
  MvPowerSeries (Fin 2) k ⧸ formalNodeIdeal k

/-- Restriction to the two axes, by killing the complementary variable on each branch.
Source: Stacks Project, Tag 0C4A, Case I.
(blueprint: lem-trf-formal-node-axes-total-fractions) -/
def formalNodeAxisMap (k : Type u) [Field k] :
    MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k × PowerSeries k :=
  (killCompl (R := k)
    ⟨fun (_ : Unit) ↦ (0 : Fin 2), Function.injective_of_subsingleton _⟩).prod
    (killCompl (R := k)
      ⟨fun (_ : Unit) ↦ (1 : Fin 2), Function.injective_of_subsingleton _⟩)

/-- The subalgebra S of branch pairs with equal constant coefficients, using Mathlib's
algebra equalizer and its inherited algebra structure.
Source: Stacks Project, Tag 0C4A, Case I.
(blueprint: lem-trf-formal-node-axes-total-fractions) -/
def formalNodeAxesSubalgebra (k : Type u) [Field k] :
    Subalgebra k (PowerSeries k × PowerSeries k) :=
  AlgHom.equalizer
    (({ PowerSeries.constantCoeff with commutes' := PowerSeries.constantCoeff_C } :
      PowerSeries k →ₐ[k] k).comp (AlgHom.fst k (PowerSeries k) (PowerSeries k)))
    (({ PowerSeries.constantCoeff with commutes' := PowerSeries.constantCoeff_C } :
      PowerSeries k →ₐ[k] k).comp (AlgHom.snd k (PowerSeries k) (PowerSeries k)))

/-- The coefficientwise inclusion of both power-series branches into their Laurent series.
Source: Stacks Project, Tag 0C4A, Case I; the Laurent inclusion is HahnSeries.ofPowerSeries.
(blueprint: lem-trf-formal-node-axes-total-fractions) -/
def formalNodeBranchesToLaurent (k : Type u) [Field k] :
    PowerSeries k × PowerSeries k →+* LaurentSeries k × LaurentSeries k :=
  RingHom.prodMap (HahnSeries.ofPowerSeries ℤ k) (HahnSeries.ofPowerSeries ℤ k)

/-- Axes, regular elements, and total fractions of the formal split node.
Source: Stacks Project, Tag 0C4A, proof of lemma-2-branches-delta-1, Case I.
(blueprint: lem-trf-formal-node-axes-total-fractions)

Proof plan:
1. In the Cauchy product only coefficients on a given axis contribute to that axis.
   Both axis restrictions vanish exactly for series divisible by uv: shift the coefficient
   a_(i+1,j+1) to degree (i,j) to factor out uv.
2. Axis restrictions have the same constant. Conversely, for equal-constant (f,g),
   the series f(u)+g(v)-c restricts to (f,g). This gives the inverse on the quotient.
3. By lem-weil-pbc-power-series-domain both branch rings are domains. A pair with
   both components nonzero multiplies injectively. If its first (resp. second) component
   vanishes, the nonzero pair (u,0) (resp. (0,v)) annihilates it. In particular (u,v)
   is regular, including in positive characteristic.
4. The Laurent inclusions are injective (def-weil-pbc-laurent-series), and both Laurent
   rings are fields (lem-weil-pbc-laurent-series-field). Regular elements therefore map
   to units. The localization universal property (lem-weil-pbc-ring-localization-universal-property)
   extends the axis embedding. A fraction mapping to zero has zero numerator, so this
   extension is injective and respects constants.
5. Shift any Laurent pair by (u^N,v^N), with N large enough that both shifted series
   have zero constant. They belong to S and their denominator is regular, giving
   surjectivity. For a power-series pair (f,g), (uf,vg)/(u,v) gives its inclusion into
   the total fraction ring. This agrees on R with r/1 and with the Laurent inclusions.
-/
theorem formalNode_axes_totalFractions (k : Type u) [Field k] :
    RingHom.ker (formalNodeAxisMap k).toRingHom = formalNodeIdeal k ∧
    Set.range (formalNodeAxisMap k) = (formalNodeAxesSubalgebra k :
      Set (PowerSeries k × PowerSeries k)) ∧
    ∃ e : FormalNodeRing k ≃ₐ[k] formalNodeAxesSubalgebra k,
      (∀ h : MvPowerSeries (Fin 2) k,
        (e (Ideal.Quotient.mk (formalNodeIdeal k) h) : PowerSeries k × PowerSeries k) =
          formalNodeAxisMap k h) ∧
      (∀ r : FormalNodeRing k,
        Function.Injective (fun x : FormalNodeRing k ↦ r * x) ↔
          (e r).val.1 ≠ 0 ∧ (e r).val.2 ≠ 0) ∧
      (∃ s : formalNodeAxesSubalgebra k,
        (s : PowerSeries k × PowerSeries k) = (PowerSeries.X, PowerSeries.X) ∧
        Function.Injective (fun x : formalNodeAxesSubalgebra k ↦ s * x)) ∧
      ∃ Φ : FractionRing (FormalNodeRing k) ≃ₐ[k] LaurentSeries k × LaurentSeries k,
        (∀ r : FormalNodeRing k,
          Φ (algebraMap (FormalNodeRing k) (FractionRing (FormalNodeRing k)) r) =
            formalNodeBranchesToLaurent k (e r).val) ∧
        ∃ ι : PowerSeries k × PowerSeries k →ₐ[k] FractionRing (FormalNodeRing k),
          Function.Injective ι ∧
          (∀ p : PowerSeries k × PowerSeries k,
            Φ (ι p) = formalNodeBranchesToLaurent k p) ∧
          (∀ r : FormalNodeRing k,
            ι (e r).val = algebraMap (FormalNodeRing k) (FractionRing (FormalNodeRing k)) r) := by
  sorry

end MvPowerSeries
