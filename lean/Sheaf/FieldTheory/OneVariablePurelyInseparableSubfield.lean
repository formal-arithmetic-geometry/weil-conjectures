module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Sheaf.FieldTheory.FieldTower
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.LinearAlgebra.Dimension.Free
import Sheaf.AlgebraicGeometry.Curve.AlgClosedCurveModel

/-!
# Purely inseparable subfields of a one-variable function field

Source: Stacks Project, Curves, Tags 0CCX and 0CCY, the field-theoretic
content of their proofs over an algebraically closed base field
(blueprint: lem-sfb-one-variable-purely-inseparable-subfield).

The intermediate field records the given inclusions. Equality of its underlying
set with the range of the power map is equality of the actual subfields in `L`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IntermediateField

/-- A finite purely inseparable subfield of a one-variable function field over an
algebraically closed field is a power subfield, with the corresponding power degree.

Source: Stacks Project, Curves, Tags 0CCX (lemma-purely-inseparable) and 0CCY
(lemma-inseparable-deg-p-smooth), specialized to algebraically closed `k`
(blueprint: lem-sfb-one-variable-purely-inseparable-subfield).

Proof plan:
1. Positive characteristic of a field is prime: a nontrivial factorization would
   give nonzero factors with zero product. Apply
   lem-weil-pbc-purely-inseparable-pth-root-tower to obtain
   E = F_0 < F_1 < ... < F_r = L, each step adjoining a p-th root with degree p.
   Append these roots to the finite field generators of E/k. Each F_i/E is
   algebraic, since a suitable p-power of every element lies in E, so that the
   element satisfies X^(p^m) minus its p-power. The transcendence-degree tower
   formula, lem-kun-transcendence-degree-tower, gives trdeg_k F_i = 1.
2. By lem-trf-algclosed-curve-model each F_i has a smooth proper integral curve
   model over k. Apply lem-sfb-smooth-curve-function-field-p-basis to this model
   to get [F_i : F_i^p] = p. The k-isomorphism between its function field and F_i
   carries powers to powers and hence power subfields to power subfields;
   applying the isomorphism and its inverse to linear combinations transports
   both the spanning and linear independence of the stated basis.
3. Write an element of F_i = F_{i-1}(alpha_i) as P(alpha_i)/Q(alpha_i).
   Its p-th power belongs to F_{i-1}, because alpha_i^p does. Powers commute
   with sums, products and inverses, so F_i^p is a subfield of F_{i-1}.
   Any F_i^p-linearly independent family in F_{i-1} stays independent in F_i,
   so F_{i-1}/F_i^p is finite. Degree multiplicativity
   (lem-weil-pbc-field-degree-multiplicativity) gives
   p = p * [F_{i-1} : F_i^p], whence the latter degree is one. The nonzero
   vector 1 spans a degree-one extension, so F_{i-1} = F_i^p inside L.
4. Descending induction gives F_{r-j} = L^(p^j), since taking p-th powers
   composes the power maps. At j = r this gives E = L^(p^r).
   Multiplying all the degree-p steps gives [L : E] = p^r. The empty tower
   r = 0 gives E = L and degree one. -/
theorem exists_pow_eq_of_purelyInseparable_of_trdeg_one
    (k : Type u) (L : Type v) [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
    (p : ℕ) [CharP k p] (hp : 0 < p) (E : IntermediateField k L)
    (hfgE : (⊤ : IntermediateField k E).FG) (hfgL : (⊤ : IntermediateField k L).FG)
    (htrdegE : Algebra.trdeg k E = 1) (htrdegL : Algebra.trdeg k L = 1)
    [Module.Finite E L] [IsPurelyInseparable E L] :
    ∃ r : ℕ, FieldExtension.degree E L = ((p ^ r : ℕ) : WithTop ℕ) ∧
      (E : Set L) = Set.range (fun x : L ↦ x ^ (p ^ r)) := by
  sorry

end IntermediateField
