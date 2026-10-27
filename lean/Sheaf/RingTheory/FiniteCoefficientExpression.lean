module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Topology.Constructions

/-!
# Finite expressions of formal coefficient operators

Source: the coefficient-family construction in the proof of
lem-trf-formal-coefficient-operator-base-change, Steps 1--4 and 8; the generic algebra
input to Bierstone--Milman 1997, Remark 9.11
(blueprint: def-trf-finite-coefficient-expression).

Expressions have a finite tuple size and a finite variable set at each boundary.
A partial coefficient test fixes the exponents outside its retained variables.
Specified inverse matrices are stored as ordinary matrices, never chosen anew.
-/

@[expose] public section

universe u v

namespace MvPowerSeries

/-- A partial coefficient test: retain `kept` variables via `inclusion`, and fix the
other exponents to `fixed`. Source: coefficient-operator base change, Step 1
(blueprint: def-trf-finite-coefficient-expression). -/
structure FormalCoefficientTest (n : ℕ) where
  kept : ℕ
  inclusion : Fin kept ↪ Fin n
  fixed : Fin n →₀ ℕ
  fixed_retained : ∀ j : Fin kept, fixed (inclusion j) = 0

/-- Partial extraction as a full series in the retained variables. Source:
coefficient-operator base change, Step 1
(blueprint: def-trf-finite-coefficient-expression). -/
noncomputable def FormalCoefficientTest.eval {n : ℕ} (D : FormalCoefficientTest n)
    {R : Type u} [CommRing R] (H : MvPowerSeries (Fin n) R) :
    MvPowerSeries (Fin D.kept) R :=
  fun γ ↦ coeff (D.fixed + γ.mapDomain D.inclusion) H

/-- The finite operator grammar, indexed by source variables/tuple size and target
variables/tuple size. Source: coefficient-operator base change, Steps 1--2
(blueprint: def-trf-finite-coefficient-expression). -/
inductive FiniteCoefficientExpression (R : Type u) : ℕ → ℕ → ℕ → ℕ → Type u
  | identity {n k : ℕ} : FiniteCoefficientExpression R n k n k
  | add {n k m l : ℕ} (A B : FiniteCoefficientExpression R n k m l) :
      FiniteCoefficientExpression R n k m l
  | comp {n k m l p h : ℕ} (B : FiniteCoefficientExpression R m l p h)
      (A : FiniteCoefficientExpression R n k m l) : FiniteCoefficientExpression R n k p h
  | multiply {n k : ℕ} (F : Fin k → MvPowerSeries (Fin n) R) :
      FiniteCoefficientExpression R n k n k
  | insert {n m k : ℕ} (i : Fin n ↪ Fin m) : FiniteCoefficientExpression R n k m k
  | extract {n k : ℕ} (D : FormalCoefficientTest n) :
      FiniteCoefficientExpression R n k D.kept k
  | matrix {n k l : ℕ} (M : Matrix (Fin l) (Fin k) R) :
      FiniteCoefficientExpression R n k n l

/-- Evaluation by the specified operations, with finite sums for matrix products.
Source: coefficient-operator base change, Step 1
(blueprint: def-trf-finite-coefficient-expression). -/
noncomputable def FiniteCoefficientExpression.eval {R : Type u} [CommRing R]
    {n k m l : ℕ} (A : FiniteCoefficientExpression R n k m l) :
    (Fin k → MvPowerSeries (Fin n) R) → (Fin l → MvPowerSeries (Fin m) R) :=
  match A with
  | .identity => fun H ↦ H
  | .add B C => fun H j ↦ B.eval H j + C.eval H j
  | .comp B C => fun H ↦ B.eval (C.eval H)
  | .multiply F => fun H j ↦ F j * H j
  | .insert i => fun H j ↦ rename i (H j)
  | .extract D => fun H j ↦ D.eval (H j)
  | .matrix M => fun H i ↦ ∑ j, M i j • H j

/-- Transport the syntax by applying the homomorphism to each stored scalar or
full formal series. Source: coefficient-operator base change, Steps 2--3
(blueprint: def-trf-finite-coefficient-expression). -/
noncomputable def FiniteCoefficientExpression.map {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (σ : R →+* S) {n k m l : ℕ}
    (A : FiniteCoefficientExpression R n k m l) : FiniteCoefficientExpression S n k m l :=
  match A with
  | .identity => .identity
  | .add B C => .add (B.map σ) (C.map σ)
  | .comp B C => .comp (B.map σ) (C.map σ)
  | .multiply F => .multiply (fun j ↦ MvPowerSeries.map σ (F j))
  | .insert i => .insert i
  | .extract D => .extract D
  | .matrix M => .matrix (M.map σ)

/-- Evaluation on a single series, the one-component case of the tuple grammar.
Source: coefficient-operator base change, statement
(blueprint: def-trf-finite-coefficient-expression). -/
noncomputable def FiniteCoefficientExpression.scalarEval {R : Type u} [CommRing R]
    {n m : ℕ} (A : FiniteCoefficientExpression R n 1 m 1)
    (H : MvPowerSeries (Fin n) R) : MvPowerSeries (Fin m) R :=
  A.eval (fun _ ↦ H) 0

/-- Product topology with discrete scalar coefficients, also for finite tuples.
Source: coefficient-operator base change, Step 2
(blueprint: def-trf-finite-coefficient-expression). -/
@[instance_reducible]
def formalCoefficientTupleTopology (R : Type u) (n k : ℕ) :
    TopologicalSpace (Fin k → MvPowerSeries (Fin n) R) :=
  @Pi.topologicalSpace (Fin k) (fun _ ↦ MvPowerSeries (Fin n) R)
    (fun _ ↦ @Pi.topologicalSpace (Fin n →₀ ℕ) (fun _ ↦ R) (fun _ ↦ ⊥))

/-- The common kernel is defined by vanishing of the full extracted series.
Source: coefficient-operator base change, Step 4
(blueprint: def-trf-finite-coefficient-expression). -/
def formalCoefficientKernel {R : Type u} [CommRing R] {n : ℕ}
    {ι : Type v} (D : ι → FormalCoefficientTest n) (H : MvPowerSeries (Fin n) R) : Prop :=
  ∀ j : ι, (D j).eval H = 0

/-- Projection means image containment and pointwise fixing of the common kernel.
Source: coefficient-operator base change, Step 4
(blueprint: def-trf-finite-coefficient-expression). -/
def FiniteCoefficientExpression.IsKernelProjection {R : Type u} [CommRing R] {n : ℕ}
    (P : FiniteCoefficientExpression R n 1 n 1) {ι : Type v}
    (D : ι → FormalCoefficientTest n) : Prop :=
  (∀ H, formalCoefficientKernel D (P.scalarEval H)) ∧
    (∀ H, formalCoefficientKernel D H → P.scalarEval H = H)

/-- The ideal-valued correction on unrestricted series. Source: coefficient-operator
base change, Step 7 (blueprint: def-trf-finite-coefficient-expression). -/
def FiniteCoefficientExpression.HasIdealCorrection {R : Type u} [CommRing R]
    {n q : ℕ} (P : FiniteCoefficientExpression R n 1 n 1)
    (f : Fin q → MvPowerSeries (Fin n) R) : Prop :=
  ∀ H : MvPowerSeries (Fin n) R, P.scalarEval H - H ∈ Ideal.span (Set.range f)

/-- Regroup an iterated formal series by its two exponent families, without a
convergence assumption. Source: coefficient-operator base change, Step 8
(blueprint: def-trf-finite-coefficient-expression). -/
noncomputable def flattenFormalCoefficients {R : Type u} [CommRing R] {x t : ℕ}
    (H : MvPowerSeries (Fin t) (MvPowerSeries (Fin x) R)) :
    MvPowerSeries (Fin x ⊕ Fin t) R :=
  fun d ↦ coeff (Finsupp.sumFinsuppEquivProdFinsupp d).1
    (coeff (Finsupp.sumFinsuppEquivProdFinsupp d).2 H)

/-- Inverse regrouping by the two exponent families. Source: coefficient-operator
base change, Step 8 (blueprint: def-trf-finite-coefficient-expression). -/
noncomputable def unflattenFormalCoefficients {R : Type u} [CommRing R] {x t : ℕ}
    (H : MvPowerSeries (Fin x ⊕ Fin t) R) :
    MvPowerSeries (Fin t) (MvPowerSeries (Fin x) R) :=
  fun e d ↦ coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (d, e)) H

end MvPowerSeries
