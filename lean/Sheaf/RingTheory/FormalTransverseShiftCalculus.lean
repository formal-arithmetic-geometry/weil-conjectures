module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Data.Nat.Choose.Sum
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation

/-!
# Formal transverse shifts and graph factorization

Source: the agent coefficientwise calculation in steps 1--7 of
`lem-trf-formal-transverse-shift-calculus`. Stacks Project, algebra.tex,
Tag 0306 supplies power-series notation only; it does not assert this theorem.
The derivative convention is Mathlib's `MvPowerSeries.pderiv`.
(blueprint: lem-trf-formal-transverse-shift-calculus).

The two names `Y` and `Z` use the same index type: the source and target rings
are separate copies of that type. Helpers spell out substitution, unrestricted
coefficient families, and the least-index matrix construction in the node's proof.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace MvPowerSeries

/-- Images of `(W,Y)` under `Y ↦ phi(W) + Z`, with `W` fixed.
Source: the node's coefficientwise construction, step 1
(blueprint: lem-trf-formal-transverse-shift-calculus). -/
def transverseShiftVariables {R : Type u} [CommRing R] {m r : ℕ}
    (phi : Fin r → MvPowerSeries (Fin m) R) :
    Fin m ⊕ Fin r → MvPowerSeries (Fin m ⊕ Fin r) R :=
  Sum.elim (fun i ↦ X (Sum.inl i)) (fun j ↦ rename Sum.inl (phi j) + X (Sum.inr j))

/-- The formal graph shift on series without auxiliary variables.
Source: the node's coefficientwise construction, step 1. The hypothesis of zero
constant terms, in the theorem below, makes this a genuine substitution rather
than the dummy branch of `subst`
(blueprint: lem-trf-formal-transverse-shift-calculus). -/
def transverseShift {R : Type u} [CommRing R] {m r : ℕ}
    (phi : Fin r → MvPowerSeries (Fin m) R)
    (f : MvPowerSeries (Fin m ⊕ Fin r) R) : MvPowerSeries (Fin m ⊕ Fin r) R :=
  subst (transverseShiftVariables phi) f

/-- The same shift, fixing the extra tuple `T`.
Source: the node's coefficientwise construction, steps 1--2
(blueprint: lem-trf-formal-transverse-shift-calculus). -/
def transverseShiftWithAux {R : Type u} [CommRing R] {m r t : ℕ}
    (phi : Fin r → MvPowerSeries (Fin m) R)
    (F : MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) R) :
    MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) R :=
  subst (Sum.elim (fun i ↦ rename Sum.inl (transverseShiftVariables phi i))
    (fun j ↦ X (Sum.inr j))) F

/-- Evaluation on the graph `Y = phi(W)`.
Source: the node's coefficientwise construction, steps 1, 4--5
(blueprint: lem-trf-formal-transverse-shift-calculus). -/
def transverseGraphEval {R : Type u} [CommRing R] {m r : ℕ}
    (phi : Fin r → MvPowerSeries (Fin m) R)
    (f : MvPowerSeries (Fin m ⊕ Fin r) R) : MvPowerSeries (Fin m) R :=
  subst (Sum.elim X phi) f

/-- Assemble the arbitrary family `f_eta(W,Y)` into `sum_eta f_eta T^eta`.
Each coefficient is read directly, so there is no support or degree restriction.
Source: the node's coefficient-family construction, step 2
(blueprint: lem-trf-formal-transverse-shift-calculus). -/
def transverseCoefficientFamily {R : Type u} [CommRing R] {m r t : ℕ}
    (f : (Fin t →₀ ℕ) → MvPowerSeries (Fin m ⊕ Fin r) R) :
    MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) R :=
  fun d ↦ coeff (d.comapDomain Sum.inl Sum.inl_injective.injOn)
    (f (d.comapDomain Sum.inr Sum.inr_injective.injOn))

/-- Extract `[Z^delta T^gamma]F` as a series in `W`.
Source: the node's coefficient-family construction, steps 2--4
(blueprint: lem-trf-formal-transverse-shift-calculus). -/
def transverseCoefficient {R : Type u} [CommRing R] {m r t : ℕ}
    (delta : Fin r →₀ ℕ) (gamma : Fin t →₀ ℕ)
    (F : MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) R) : MvPowerSeries (Fin m) R :=
  fun alpha ↦ coeff ((alpha.sumElim delta).sumElim gamma) F

/-- The factorial-normalized derivative evaluated along the graph.
The derivative itself is the existing `HilbertCoefficient.iteratedPartial`.
Source: the node's coefficientwise calculation, step 4
(blueprint: lem-trf-formal-transverse-shift-calculus). -/
def transverseTaylorCoefficient {L : Type u} [Field L] {m r : ℕ}
    (phi : Fin r → MvPowerSeries (Fin m) L) (delta : Fin r →₀ ℕ)
    (f : MvPowerSeries (Fin m ⊕ Fin r) L) : MvPowerSeries (Fin m) L :=
  ((∏ j : Fin r, (delta j).factorial : ℕ) : L)⁻¹ •
    transverseGraphEval phi
      (AlgebraicGeometry.HilbertCoefficient.iteratedPartial
        (AlgebraicGeometry.HilbertCoefficient.fullVertex m delta) f)

/-- Allocate each nonzero transverse monomial of `g_i` to its least positive
transverse index. In column `j`, the coefficient at `d` comes from `d + e_j`
if all earlier transverse exponents vanish, and is otherwise zero.
Source: the node's explicit construction of `V`, step 5
(blueprint: lem-trf-formal-transverse-shift-calculus). -/
def transverseAllocatedMatrix {R : Type u} [CommRing R] {m r : ℕ}
    (g : Fin r → MvPowerSeries (Fin m ⊕ Fin r) R) :
    Matrix (Fin r) (Fin r) (MvPowerSeries (Fin m ⊕ Fin r) R) :=
  fun i j d ↦ if ∀ k : Fin r, k < j → d (Sum.inr k) = 0 then
    coeff (d + Finsupp.single (Sum.inr j) 1) (g i) else 0

/-- The specified choice `U = S_{-phi}(V)`, where `V` is the least-index
allocation matrix of `S_phi(h)`. This is real coefficient data, independent
of a choice of inverse or an existence proof.
Source: the node's explicit matrix construction, steps 5--7
(blueprint: lem-trf-formal-transverse-shift-calculus). -/
def transverseGraphMatrix {R : Type u} [CommRing R] {m r : ℕ}
    (phi : Fin r → MvPowerSeries (Fin m) R)
    (h : Fin r → MvPowerSeries (Fin m ⊕ Fin r) R) :
    Matrix (Fin r) (Fin r) (MvPowerSeries (Fin m ⊕ Fin r) R) :=
  fun i j ↦ transverseShift (fun k ↦ -phi k)
    (transverseAllocatedMatrix (fun k ↦ transverseShift phi (h k)) i j)

/-- Formal transverse shift, factorial coefficient extraction for unrestricted
families, and invertible graph factorization.

Source: the node's agent coefficientwise calculation, steps 1--6; Stacks 0306
is notation only (blueprint: lem-trf-formal-transverse-shift-calculus).

Proof plan:
1. Use power-series completeness and `exists_unique_adic_evaluation` to evaluate
   at `(W,phi+Z,T)` and `(W,Y-phi,T)`. Uniqueness makes them inverse algebra
   maps, continuous for the full variable ideals. The same works without `T`.
2. Assemble the family by its coefficients. Since the shift fixes `T`, extracting
   `T^gamma` selects exactly `f_gamma`, with no support assumption.
3. Apply the binomial theorem to each `(phi_j+Z_j)^beta_j`. At a fixed `W^mu`,
   only pairs with `|alpha|+|beta|-|delta| ≤ |mu|` contribute, since phi is in
   `(W)`. Thus every coefficient rearrangement is finite.
4. Iterating the partial-derivative coefficient rule gives falling factorials.
   Divide by the nonzero delta factorial in characteristic zero; the resulting
   binomial factors are exactly those of step 3.
5. Shift `h` to `g`. Graph vanishing kills its transverse constant coefficient.
   Least-index allocation gives `g=VZ`, and step 4 identifies the constant
   matrix of `V` with the transverse Jacobian.
6. Apply `lem-trf-shift-filtered-matrix-inverse` with empty weight tuple (`n=0`)
   to invert `V`. Transport it back by the inverse shift to obtain the specified
   `U` and its inverse. Multiplying the vector identities by these inverses
   proves both ideal inclusions. The shift takes `Y-phi` to `Z`.
All constructions include empty variable sets, the empty matrix, and delta zero. -/
theorem formal_transverse_shift_calculus {L : Type u} [Field L] [CharZero L]
    (m r t : ℕ) (phi : Fin r → MvPowerSeries (Fin m) L)
    (hphi : ∀ j : Fin r,
      phi j ∈ Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) L))) :
    ∃ S : MvPowerSeries (Fin m ⊕ Fin r) L ≃ₐ[L]
        MvPowerSeries (Fin m ⊕ Fin r) L,
    ∃ ST : MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) L ≃ₐ[L]
        MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) L,
      (∀ f, S f = transverseShift phi f) ∧
      (∀ f, S.symm f = transverseShift (fun j ↦ -phi j) f) ∧
      (∀ F, ST F = transverseShiftWithAux phi F) ∧
      (∀ F, ST.symm F = transverseShiftWithAux (fun j ↦ -phi j) F) ∧
      (∀ N : ℕ, ∃ M : ℕ,
        ∀ f ∈ (Ideal.span (Set.range
          (X : Fin m ⊕ Fin r → MvPowerSeries (Fin m ⊕ Fin r) L))) ^ M,
          S f ∈ (Ideal.span (Set.range X)) ^ N ∧
          S.symm f ∈ (Ideal.span (Set.range X)) ^ N) ∧
      (∀ N : ℕ, ∃ M : ℕ,
        ∀ F ∈ (Ideal.span (Set.range
          (X : (Fin m ⊕ Fin r) ⊕ Fin t →
            MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) L))) ^ M,
          ST F ∈ (Ideal.span (Set.range X)) ^ N ∧
          ST.symm F ∈ (Ideal.span (Set.range X)) ^ N) ∧
      (∀ (f : (Fin t →₀ ℕ) → MvPowerSeries (Fin m ⊕ Fin r) L)
          (gamma : Fin t →₀ ℕ) (delta : Fin r →₀ ℕ),
        transverseCoefficient delta gamma (ST (transverseCoefficientFamily f)) =
          transverseTaylorCoefficient phi delta (f gamma)) ∧
      (∀ h : Fin r → MvPowerSeries (Fin m ⊕ Fin r) L,
        (∀ i : Fin r, transverseGraphEval phi (h i) = 0) →
        IsUnit (Matrix.of (fun i j : Fin r ↦ constantCoeff (pderiv L (Sum.inr j) (h i)))) →
        IsUnit (transverseGraphMatrix phi h) ∧
        h = (transverseGraphMatrix phi h).mulVec
          (fun j ↦ X (Sum.inr j) - rename Sum.inl (phi j)) ∧
        Ideal.span (Set.range h) = Ideal.span
          (Set.range (fun j ↦ X (Sum.inr j) - rename Sum.inl (phi j))) ∧
        Ideal.map S.toRingEquiv.toRingHom (Ideal.span (Set.range h)) =
          Ideal.span (Set.range (fun j : Fin r ↦ X (Sum.inr j)))) := by
  sorry

/-- Every operation in formal transverse shift calculus commutes with coefficient
field extension, including the specified choice of graph matrix.

Source: the node's agent coefficientwise calculation, step 7
(blueprint: lem-trf-formal-transverse-shift-calculus).

Proof plan: apply the coefficient map to the finite convolution and truncation
formulas in steps 1--4 of the node. It commutes with each substitution, and with
its inverse (replace phi by -phi). Family assembly and extraction read a single
coefficient. Derivatives multiply by natural scalars, and a field homomorphism
preserves factorials and their inverses, proving compatibility of the Taylor
expression. The least-index rule depends only on the exponent, so extension
commutes with allocation and hence with `U=S_{-phi}(V)`. Applying the coefficient
map to an inverse of `U` preserves both inverse identities. This argument also
covers identity extensions and every empty-tuple case. -/
theorem formal_transverse_shift_coefficient_extension
    {L : Type u} {K : Type v} [Field L] [CharZero L] [Field K]
    (iota : L →+* K) (m r t : ℕ) (phi : Fin r → MvPowerSeries (Fin m) L)
    (hphi : ∀ j : Fin r,
      phi j ∈ Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) L))) :
    (∀ f : MvPowerSeries (Fin m ⊕ Fin r) L,
      map iota (transverseShift phi f) =
        transverseShift (fun j ↦ map iota (phi j)) (map iota f)) ∧
    (∀ f : MvPowerSeries (Fin m ⊕ Fin r) L,
      map iota (transverseShift (fun j ↦ -phi j) f) =
        transverseShift (fun j ↦ -map iota (phi j)) (map iota f)) ∧
    (∀ F : MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) L,
      map iota (transverseShiftWithAux phi F) =
        transverseShiftWithAux (fun j ↦ map iota (phi j)) (map iota F)) ∧
    (∀ F : MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) L,
      map iota (transverseShiftWithAux (fun j ↦ -phi j) F) =
        transverseShiftWithAux (fun j ↦ -map iota (phi j)) (map iota F)) ∧
    (∀ f : (Fin t →₀ ℕ) → MvPowerSeries (Fin m ⊕ Fin r) L,
      map iota (transverseCoefficientFamily f) =
        transverseCoefficientFamily (fun gamma ↦ map iota (f gamma))) ∧
    (∀ (delta : Fin r →₀ ℕ) (gamma : Fin t →₀ ℕ)
        (F : MvPowerSeries ((Fin m ⊕ Fin r) ⊕ Fin t) L),
      map iota (transverseCoefficient delta gamma F) =
        transverseCoefficient delta gamma (map iota F)) ∧
    (∀ (delta : Fin r →₀ ℕ) (f : MvPowerSeries (Fin m ⊕ Fin r) L),
      map iota (transverseTaylorCoefficient phi delta f) =
        transverseTaylorCoefficient (fun j ↦ map iota (phi j)) delta (map iota f)) ∧
    (∀ h : Fin r → MvPowerSeries (Fin m ⊕ Fin r) L,
      (∀ i : Fin r, transverseGraphEval phi (h i) = 0) →
      IsUnit (Matrix.of (fun i j : Fin r ↦ constantCoeff (pderiv L (Sum.inr j) (h i)))) →
      ∀ i j : Fin r, map iota (transverseGraphMatrix phi h i j) =
        transverseGraphMatrix (fun k ↦ map iota (phi k)) (fun k ↦ map iota (h k)) i j) := by
  sorry

end MvPowerSeries
