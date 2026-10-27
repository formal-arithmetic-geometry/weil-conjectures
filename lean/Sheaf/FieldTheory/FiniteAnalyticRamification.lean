/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.FieldTheory.AnalyticRamification
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import WeilConjectures.RingTheory.HenselianLocalRootLifting

/-!
# Finite analytic ramification invariants and residue lifts

Source: Temkin, Stable modification of relative curves, §2.1, Lemma 2.1.5,
and §6.2 opening (blueprint: lem-trf-valued-finite-ramification-calculus).

The statements cover existence and uniqueness of the extending norm, completeness,
finite positive invariants and prime-power defect, towers, tame composita,
unramified residue lifts, immediate base change, and relative invariant stability.
-/

@[expose] public section

set_option autoImplicit false

open scoped NNReal

universe u v w z

namespace AnalyticRamification

/-- Finite extensions admit a unique extending nonarchimedean real absolute value.
Source: Temkin §2.1, analytic fields (blueprint: lem-trf-valued-finite-ramification-calculus).
Proof: lem-trf-spectral-norm-algebraic-extension constructs the multiplicative spectral
norm. The uniqueness theorem lem-sfb-algebraic-absolute-value-unique identifies any
extending absolute value with this spectral norm; no separability is required. -/
theorem exists_unique_extending_absoluteValue
    (K : Type u) (L : Type v) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    ∃ a : AbsoluteValue L ℝ, IsNonarchimedean a ∧
      (∀ x : K, a (algebraMap K L x) = ‖x‖) ∧
      (∀ b : AbsoluteValue L ℝ,
        (∀ x : K, b (algebraMap K L x) = ‖x‖) → b = a) := by
  sorry

/-- The finite extension with its compatible norm is complete.
Source: Temkin §2.1 (blueprint: lem-trf-valued-finite-ramification-calculus).
Proof: regard L as a finite-dimensional normed K-vector space and apply
lem-per-finite-normed-space-complete, namely FiniteDimensional.complete K L. -/
theorem finite_extension_complete
    (K : Type u) (L : Type v) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
    [NormedAlgebra K L] [FiniteDimensional K L] : CompleteSpace L := by
  sorry

/-- The invariants are finite positive and the rational defect is a characteristic power.
Source: Temkin Lemma 2.1.5(iv) (blueprint: lem-trf-valued-finite-ramification-calculus).
Proof:
1. The fundamental inequality lem-trf-valued-extension-degree-bound gives positive
   finite e,f and ef ≤ [L:K]. Thus the quotient defining d is at least one.
2. By lem-trf-separable-valued-completion-factors the valuation ring of complete K
   is henselian. For finite Galois N/K apply lem-trf-galois-graded-wild-kernel:
   the tame fixed field has defect one, and the remaining degree and indices are
   p-powers. Their ratio is a nonnegative p-power by the fundamental inequality.
3. Embed a finite separable L/K into a finite Galois N/K. By
   lem-dl-a1-galois-over-intermediate, N/L is Galois. Multiplicativity and d≥1
   show that d(L/K)=d(N/K)/d(N/L) is again a nonnegative p-power.
4. For arbitrary L/K take its separable closure S inside L. By
   lem-weil-pbc-separable-first-purely-inseparable, L/S is purely inseparable.
   The root tower lem-weil-pbc-purely-inseparable-pth-root-tower makes its degree,
   value-group index and residue degree powers of the field characteristic p.
   Divide and use the inequality to get a nonnegative exponent; multiply by d(S/K).
5. In residue characteristic zero the wild kernel is trivial and d=1. In positive
   field characteristic its value is also the residue characteristic. -/
theorem finite_ramification_invariants
    (K : Type u) (L : Type v) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NontriviallyNormedField L] [IsUltrametricDist L]
    [NormedAlgebra K L] [FiniteDimensional K L] :
    Finite (values L ⧸ (values K).subgroupOf (values L)) ∧
      @Module.Finite (residue K) (residue L) _ _
        (residueAlgebra (algebraMap K L) (norm_algebraMap' L)).toModule ∧
      0 < ramificationIndex K L ∧ 0 < residueDegree K L ∧
      (ringChar (residue K) = 0 → defect K L = 1) ∧
      (ringChar (residue K) ≠ 0 →
        ∃ n : ℕ, defect K L = (ringChar (residue K) : ℚ) ^ n) := by
  sorry

/-- Multiplicativity and the two directions of tame permanence in finite towers.
Source: Temkin §2.1, Lemma 2.1.5 (blueprint: lem-trf-valued-finite-ramification-calculus).
Proof: products of value coset representatives enumerate the composite quotient.
Products of residue-field bases, and of field bases, are bases in the corresponding
composite towers; divide the three multiplicativity identities to obtain that for d.
Positive integral defects multiplying to one are both one. Ramification indices in
subextensions divide the composite index; prime-to-p integers are closed under
products and divisors. Residue separability descends and ascends in towers, using
lem-zl-separable-permanence for transitivity. In characteristic zero omit the
prime-to-p condition, exactly as in the numerical definition. -/
theorem finite_ramification_tower
    (K : Type u) (L : Type v) (M : Type w)
    [NontriviallyNormedField K] [NontriviallyNormedField L] [NontriviallyNormedField M]
    [CompleteSpace K] [CompleteSpace L] [CompleteSpace M]
    [IsUltrametricDist K] [IsUltrametricDist L] [IsUltrametricDist M]
    [NormedAlgebra K L] [NormedAlgebra L M] [NormedAlgebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M] :
    ramificationIndex K M = ramificationIndex K L * ramificationIndex L M ∧
      residueDegree K M = residueDegree K L * residueDegree L M ∧
      defect K M = defect K L * defect L M ∧
      (IsTame K M ↔ IsTame K L ∧ IsTame L M) := by
  sorry

/-- Tame finite extensions remain tame after finite complete base change in a compositum.
Source: Temkin §2.1, maximal tame extension; Gabber--Ramero §6.2.14--18
(blueprint: lem-trf-valued-finite-ramification-calculus).
Proof: lem-trf-tame-root-envelope embeds L in a finite extension generated by an
unramified field and prime-to-residue-characteristic radicals. Base change its
integer-ring finite etale algebra using lem-weil-pbc-etale-ring-base-change.
The local factor selected by the compositum's valuation has finite etale integer
ring by lem-trf-henselian-valuation-etale-local-factors. The same radical equations
and roots of unity work over this field. The converse root-envelope criterion
makes the upper radical envelope tame; its intermediate compositum is tame by
finite_ramification_tower. A field compositum of finite extensions is finite. -/
theorem tame_compositum
    (K : Type u) (L : Type v) (M : Type w) (D : Type z)
    [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NontriviallyNormedField M] [NontriviallyNormedField D]
    [CompleteSpace K] [CompleteSpace L] [CompleteSpace M] [CompleteSpace D]
    [IsUltrametricDist K] [IsUltrametricDist L]
    [IsUltrametricDist M] [IsUltrametricDist D]
    [NormedAlgebra K L] [NormedAlgebra K M] [NormedAlgebra K D]
    [NormedAlgebra L D] [NormedAlgebra M D]
    [IsScalarTower K L D] [IsScalarTower K M D]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (hcomp : IntermediateField.adjoin K
      (Set.range (algebraMap L D) ∪ Set.range (algebraMap M D)) = ⊤)
    (htame : IsTame K L) : Module.Finite M D ∧ IsTame M D := by
  sorry

/-- A separable residue extension is realized by an unramified intermediate field.
Source: Temkin proof of Lemma 2.1.5 (blueprint: lem-trf-valued-finite-ramification-calculus).
Proof: choose a residue primitive element by
lem-weil-pbc-finite-separable-extension-primitive-element and lift its monic minimal
polynomial to the ground integer ring. Henselianity of the complete upper integer
ring follows from lem-trf-separable-valued-completion-factors. Lift its simple residue
root by lem-weil-pbc-henselian-local-root-lifting and put U=K(b). The residue of b
generates the upper residue field, so the canonical U-to-L residue map is surjective.
The degree of U/K is at most the lifted polynomial degree f. The fundamental
inequality lem-trf-valued-extension-degree-bound forces [U:K]=f and e=1, hence d=1.
The residue extension is separable. When f=1 take U=K. -/
theorem exists_unramified_residue_lift
    (K : Type u) (L : Type v) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NontriviallyNormedField L] [CompleteSpace L]
    [IsUltrametricDist L] [NormedAlgebra K L] [FiniteDimensional K L]
    (hsep : HasSeparableResidue K L) :
    ∃ U : IntermediateField K L, IsUnramified K U ∧
      Function.Surjective (residueMap U.val.toRingHom (fun _ ↦ rfl)) := by
  sorry

/-- Finite immediate extensions preserve immediacy and degree after tame base change.
Source: Temkin §2.1, orthogonal basis calculus
(blueprint: lem-trf-valued-finite-ramification-calculus).
Proof: choose value coset representatives t_i and lifts u_j of a residue basis of M/K.
Tameness gives ef=[M:K]. The products t_i u_j form an orthogonal K-basis: distinct
value cosets cannot cancel, and within one coset residue independence prevents
cancellation. Immediacy of L/K gives exactly the same argument over L, so these
vectors remain independent. Their L-span is the image of L tensor_K M, a finite
dimensional domain, hence a field, equal to D by the compositum hypothesis. Thus
[D:L]=[M:K] and the field tower formula gives [D:M]=[L:K]. Immediacy also lets each
nonzero L-coefficient be approximated by a K-element with strictly smaller error.
Approximate the finitely many coefficients in an expansion of x in this basis.
Orthogonality produces y in M with |x-y|<|x|, hence equal value and equal unit residue.
This proves equality of value groups and surjectivity on residues for D/M. -/
theorem immediate_tame_compositum
    (K : Type u) (L : Type v) (M : Type w) (D : Type z)
    [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NontriviallyNormedField M] [NontriviallyNormedField D]
    [CompleteSpace K] [CompleteSpace L] [CompleteSpace M] [CompleteSpace D]
    [IsUltrametricDist K] [IsUltrametricDist L]
    [IsUltrametricDist M] [IsUltrametricDist D]
    [NormedAlgebra K L] [NormedAlgebra K M] [NormedAlgebra K D]
    [NormedAlgebra L D] [NormedAlgebra M D]
    [IsScalarTower K L D] [IsScalarTower K M D]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (hcomp : IntermediateField.adjoin K
      (Set.range (algebraMap L D) ∪ Set.range (algebraMap M D)) = ⊤)
    (himmediate : IsImmediate K L) (htame : IsTame K M) :
    IsImmediate M D ∧ Module.finrank M D = Module.finrank K L := by
  sorry

/-- Finite extension preserves both relative cardinal invariants; algebraically closed
residue constants force the residue fields to coincide in residual transcendence degree zero.
Source: Temkin §6.2 opening and Remark 6.2.2
(blueprint: lem-trf-valued-finite-ramification-calculus).
Proof: lem-trf-valued-extension-degree-bound makes the upper residue extension finite
algebraic. A transcendence basis of the lower residue field over the ground residue
field remains one upstairs by transitivity of algebraicity. Finite index of value
groups makes their quotients by ground values have isomorphic rationalizations:
every upper class has a positive multiple downstairs, and clearing denominators
proves injectivity. Use cardinal dimensions, without any finite rank assumption.
If the residue transcendence degree is zero and the ground residue field is
algebraically closed, both residue fields are algebraic over it and the canonical
embeddings are surjective. -/
theorem finite_extension_relative_invariants
    (k : Type u) (K : Type v) (L : Type w)
    [NontriviallyNormedField k] [NontriviallyNormedField K] [NontriviallyNormedField L]
    [CompleteSpace k] [CompleteSpace K] [CompleteSpace L]
    [IsUltrametricDist k] [IsUltrametricDist K] [IsUltrametricDist L]
    [NormedAlgebra k K] [NormedAlgebra K L] [NormedAlgebra k L]
    [IsScalarTower k K L] [FiniteDimensional K L] :
    Cardinal.lift.{w} (residueTrdeg k K) = Cardinal.lift.{v} (residueTrdeg k L) ∧
      relativeRationalRank k K = relativeRationalRank k L ∧
      (residueTrdeg k K = 0 → IsAlgClosed (residue k) →
        Function.Surjective (residueMap (algebraMap k K) (norm_algebraMap' K)) ∧
        Function.Surjective (residueMap (algebraMap k L) (norm_algebraMap' L)) ∧
        Function.Surjective (residueMap (algebraMap K L) (norm_algebraMap' L))) := by
  sorry

/-- A finite-index supergroup of a divisible subgroup of positive reals equals it.
Source: Temkin Remark 6.2.2 (blueprint: lem-trf-valued-finite-ramification-calculus).
Proof: finite index gives a positive power h^n in the lower group. Divisibility
supplies d there with d^n=h^n. Positive real n-th powering is injective for n>0,
so h=d. This proves containment in the reverse direction, hence equality. -/
theorem finite_index_divisible_values
    (G H : Subgroup (ℝ≥0)ˣ) (hGH : G ≤ H)
    (hdiv : ∀ (g : G) (n : ℕ), 0 < n → ∃ d : G, d ^ n = g)
    (hfinite : Finite (H ⧸ G.subgroupOf H)) : G = H := by
  sorry

end AnalyticRamification
