/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.RingTheory.AssociatedGradedRing
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Finite jets after coefficient extension and adjoining power series variables

Source: literature/stacks-project/algebra.tex, Tags 00DF and 00HD for tensor
exactness; the finite coefficient and multiplication argument in the DAG node
(blueprint: lem-trf-coefficient-extended-power-series-jets).

## Main definitions and statement

* `coefficientMap`, `quotientMap`: the specified inclusion and its quotient map.
* `sourceJet`, `targetJet`, `coefficients`: the jet rings and coefficient direct sum.
* `coefficientVector`: coefficients of the finite total-degree truncation.
* `coefficient_extended_power_series_jets`: jet and graded algebra comparisons.

The helper constructions spell out the specified coefficient inclusion, quotient
rings, monomials, and truncated coefficient vector. The theorem also specifies the
reduction and convolution formulas and the associated graded algebra comparison.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

open scoped TensorProduct
open DirectSum

namespace MvPowerSeries.CoefficientExtendedJets

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (e s : ℕ)

/-- Coefficient inclusion followed by inclusion of the `X` variables.
Source: the finite coefficient argument, step 1
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def coefficientMap : MvPowerSeries (Fin e) K →+* MvPowerSeries (Fin e ⊕ Fin s) L :=
  (MvPowerSeries.rename (Sum.inl : Fin e → Fin e ⊕ Fin s)).toRingHom.comp
    (MvPowerSeries.map (algebraMap K L))

/-- The original quotient `C = K[[X]]/I`.
Source: the setup of the finite coefficient argument
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
abbrev sourceRing (I : Ideal (MvPowerSeries (Fin e) K)) :=
  MvPowerSeries (Fin e) K ⧸ I

/-- The quotient by the algebraically extended ideal `I L[[X,T]]`.
Source: the finite coefficient argument, step 1
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
abbrev targetRing (I : Ideal (MvPowerSeries (Fin e) K)) :=
  MvPowerSeries (Fin e ⊕ Fin s) L ⧸ I.map (coefficientMap K L e s)

variable (I : Ideal (MvPowerSeries (Fin e) K))

/-- The actual map `j : C → D` induced by coefficient and variable inclusion.
Source: the setup of the finite coefficient argument
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def quotientMap : sourceRing K e I →+* targetRing K L e s I :=
  Ideal.quotientMap (I.map (coefficientMap K L e s)) (coefficientMap K L e s)
    Ideal.le_comap_map

/-- The image of the variables ideal in `C`.
Source: the setup of the finite coefficient argument
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def sourceIdeal : Ideal (sourceRing K e I) :=
  (Ideal.span (Set.range (MvPowerSeries.X : Fin e → MvPowerSeries (Fin e) K))).map
    (Ideal.Quotient.mk I)

/-- The image of all `X,T` variables in `D`.
Source: the setup of the finite coefficient argument
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def targetIdeal : Ideal (targetRing K L e s I) :=
  (Ideal.span (Set.range
    (MvPowerSeries.X : Fin e ⊕ Fin s → MvPowerSeries (Fin e ⊕ Fin s) L))).map
      (Ideal.Quotient.mk (I.map (coefficientMap K L e s)))

/-- The `m`th jet of `C`, including the zero jet at `m = 0`.
Source: the finite coefficient argument, steps 1 and 7
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
abbrev sourceJet (m : ℕ) := sourceRing K e I ⧸ sourceIdeal K e I ^ m

/-- The `N`th jet of `D`.
Source: the finite coefficient argument, step 1
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
abbrev targetJet (N : ℕ) := targetRing K L e s I ⧸ targetIdeal K L e s I ^ N

/-- The coefficient direct sum, indexed by `T` monomials of degree below `N`.
Source: the finite coefficient argument, steps 3--4
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
abbrev coefficients (N : ℕ) :=
  ⨁ β : {β : Fin s →₀ ℕ // β.degree < N},
    L ⊗[K] sourceJet K e I (N - β.val.degree)

/-- A pure tensor in one coefficient summand, represented by `c ∈ C`.
Source: the finite coefficient argument, step 4
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def coefficientTerm (N : ℕ) (β : Fin s →₀ ℕ) (hβ : β.degree < N)
    (l : L) (c : sourceRing K e I) : coefficients K L e s I N :=
  DirectSum.of (fun γ : {γ : Fin s →₀ ℕ // γ.degree < N} ↦
    L ⊗[K] sourceJet K e I (N - γ.val.degree)) ⟨β, hβ⟩
      (l ⊗ₜ[K] Ideal.Quotient.mk (sourceIdeal K e I ^ (N - β.degree)) c)

/-- The class of the monomial `T^β` in `D`.
Source: the finite coefficient argument, steps 4 and 9
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def tMonomial (β : Fin s →₀ ℕ) : targetRing K L e s I :=
  Ideal.Quotient.mk (I.map (coefficientMap K L e s))
    (MvPowerSeries.monomial (Finsupp.mapDomain Sum.inr β) 1)

/-- The `X` part of an exponent in the disjointly labelled `X,T` variables.
Source: the finite coefficient argument, step 3
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def xExponent (E : (Fin e ⊕ Fin s) →₀ ℕ) : Fin e →₀ ℕ :=
  Finsupp.comapDomain.addMonoidHom Sum.inl_injective E

/-- The `T` part of an exponent in the disjointly labelled `X,T` variables.
Source: the finite coefficient argument, step 3
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def tExponent (E : (Fin e ⊕ Fin s) →₀ ℕ) : Fin s →₀ ℕ :=
  Finsupp.comapDomain.addMonoidHom Sum.inr_injective E

/-- Extract the finite truncated coefficient vector. Each scalar monomial coefficient
is tensored with its `X` monomial class, in the summand indexed by its `T` exponent.
Source: the finite coefficient argument, steps 2--4
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def coefficientVector (N : ℕ) (F : MvPowerSeries (Fin e ⊕ Fin s) L) :
    coefficients K L e s I N :=
  ∑ E ∈ (MvPowerSeries.truncTotal N F).support,
    if h : (tExponent e s E).degree < N then
      coefficientTerm K L e s I N (tExponent e s E) h
        (MvPolynomial.coeff E (MvPowerSeries.truncTotal N F))
        (Ideal.Quotient.mk I (MvPowerSeries.monomial (xExponent e s E) 1))
    else 0

/-- Reduction from the `(N+1)`st jet to the `N`th jet.
Source: the finite coefficient argument, step 5
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def reduction (N : ℕ) : targetJet K L e s I (N + 1) →+* targetJet K L e s I N :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ N))

/-- Base scalars act on an associated graded ring through its degree-zero map.
This supplies the coefficient algebra structures used in the comparison, without
changing its associated graded ring or any of its pieces. It is scoped: as a global
instance it would also apply to `k = ℕ`, `ℤ` or `A`, where its module structure is not
definitionally the componentwise `DirectSum` action.
Source: the finite coefficient argument, step 9; Stacks, Algebra, Section 00JL
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
noncomputable scoped instance gradedBaseAlgebra (k : Type w) [CommRing k]
    {A : Type u} [CommRing A] [Algebra k A] (J : Ideal A) :
    Algebra k (Ideal.associatedGraded J) :=
  ((Ideal.associatedGradedRingHom J).comp (algebraMap k A)).toAlgebra

/-- The tensor algebra with the specified degree-zero action on the graded ring.
Source: the finite coefficient argument, steps 8--9
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
abbrev gradedCoefficients :=
  @TensorProduct K _ L (Ideal.associatedGraded (sourceIdeal K e I)) _ _ _
    (gradedBaseAlgebra K (sourceIdeal K e I)).toModule

/-- A homogeneous pure tensor with the specified degree-zero coefficient action.
Source: the finite coefficient argument, step 8
(blueprint: lem-trf-coefficient-extended-power-series-jets). -/
def gradedTensor (l : L) (x : Ideal.associatedGraded (sourceIdeal K e I)) :
    gradedCoefficients K L e I :=
  @TensorProduct.tmul K _ L (Ideal.associatedGraded (sourceIdeal K e I)) _ _ _
    (gradedBaseAlgebra K (sourceIdeal K e I)).toModule l x

/-- Finite jets, their transition maps and products, and the graded comparison
for an arbitrary coefficient field extension.

Source: literature/stacks-project/algebra.tex, Tags 00DF and 00HD for exactness;
the nine-step finite coefficient argument of this node
(blueprint: lem-trf-coefficient-extended-power-series-jets).

Proof plan:
1. Express the jets as quotients by `I + (X)^m` and `IS + (X,T)^N`.
   The coefficient criterion of lem-weil-pbc-power-series-combined-ideal-coefficients,
   at base ideal zero, identifies the variable ideal powers by total degree.
2. Truncated monomials identify `L ⊗ W_m(K)` with `W_m(L)`; the inverse sends each
   scalar monomial to its pure tensor. All sums are finite even for infinite `L/K`.
3. Group by the `T` exponent. The image of `IS` in the truncated series is the sum
   of the coefficient extensions of the images of `I`: truncate its finite sums
   `h_i f_i`; conversely realize a coefficient relation by `l f T^β`.
4. Apply lem-weil-pbc-tensor-right-exact to the relation-space sequence and quotient
   the direct sum componentwise. The inverse sends `l ⊗ [c]` in the `β` summand to
   `[l j(c) T^β]`, which gives precisely `coefficientVector` on representatives.
5. Lowering the total cutoff reduces each retained coefficient quotient and deletes
   the summands of `T` degree `N`. The relations from `I` reduce compatibly.
6. The Cauchy product is coefficient convolution. Changes of representatives by `I`
   land in `IS`; changes by `(X)^(N-|β|)` contribute total degree at least `N`.
   This proves the displayed product formula on generators and hence on finite sums.
7. Take kernels of successive jet reductions. Use lem-weil-pbc-module-over-field-flat,
   lem-weil-pbc-flat-tensor-exact and lem-weil-pbc-tensor-right-exact to identify each
   kernel with the tensor of the corresponding associated graded piece. Degree zero
   uses the zero jet `C/a^0 = 0`, so the boundary `|β| = n` is included.
8. Expand tensor coefficients and polynomials into their finite homogeneous sums,
   then reindex pairs `(d, β)` by `d + |β|`. The direct sum of the kernel comparisons
   gives the bijective graded linear comparison.
9. By lem-weil-pbc-associated-graded-ring-structure, homogeneous products are classes
   of products of representatives. The generator formula therefore preserves products,
   unit and scalars and uses the actual `j` when `β = 0`.
-/
theorem coefficient_extended_power_series_jets
    (hI : I ≤ Ideal.span
      (Set.range (MvPowerSeries.X : Fin e → MvPowerSeries (Fin e) K))) :
    ∃ φ : ∀ (N : ℕ), 0 < N →
        targetJet K L e s I N ≃ₗ[L] coefficients K L e s I N,
      (∀ (N : ℕ) (hN : 0 < N) (F : MvPowerSeries (Fin e ⊕ Fin s) L),
        φ N hN (Ideal.Quotient.mk (targetIdeal K L e s I ^ N)
          (Ideal.Quotient.mk (I.map (coefficientMap K L e s)) F)) =
            coefficientVector K L e s I N F) ∧
      (∀ (N : ℕ) (hN : 0 < N) (β : Fin s →₀ ℕ) (hβ : β.degree < N)
          (l : L) (c : sourceRing K e I),
        (φ N hN).symm (coefficientTerm K L e s I N β hβ l c) =
          Ideal.Quotient.mk (targetIdeal K L e s I ^ N)
            (l • (quotientMap K L e s I c * tMonomial K L e s I β))) ∧
      (∀ (N : ℕ) (hN : 0 < N) (β : Fin s →₀ ℕ) (hβ : β.degree < N + 1)
          (l : L) (c : sourceRing K e I),
        φ N hN (reduction K L e s I N
          ((φ (N + 1) (Nat.zero_lt_succ N)).symm
            (coefficientTerm K L e s I (N + 1) β hβ l c))) =
          if h : β.degree < N then coefficientTerm K L e s I N β h l c else 0) ∧
      (∀ (N : ℕ) (hN : 0 < N) (β γ : Fin s →₀ ℕ)
          (hβ : β.degree < N) (hγ : γ.degree < N)
          (l m : L) (c d : sourceRing K e I),
        φ N hN
          ((φ N hN).symm (coefficientTerm K L e s I N β hβ l c) *
            (φ N hN).symm (coefficientTerm K L e s I N γ hγ m d)) =
          if h : (β + γ).degree < N then
            coefficientTerm K L e s I N (β + γ) h (l * m) (c * d) else 0) ∧
      ∃ ψ : MvPolynomial (Fin s)
          (gradedCoefficients K L e I) ≃ₐ[L]
            Ideal.associatedGraded (targetIdeal K L e s I),
        ∀ (d : ℕ) (c : (sourceIdeal K e I ^ d : Ideal (sourceRing K e I)))
            (β : Fin s →₀ ℕ) (l : L),
          ∃ y : (targetIdeal K L e s I ^ (d + β.degree) :
              Ideal (targetRing K L e s I)),
            y.val = l • (quotientMap K L e s I c.val * tMonomial K L e s I β) ∧
            ψ (MvPolynomial.monomial β
              (gradedTensor K L e I l
                (DirectSum.of (Ideal.associatedGradedPiece (sourceIdeal K e I)) d
                  (Submodule.Quotient.mk c)))) =
              DirectSum.of (Ideal.associatedGradedPiece (targetIdeal K L e s I))
                (d + β.degree) (Submodule.Quotient.mk y) := by
  sorry

end MvPowerSeries.CoefficientExtendedJets
