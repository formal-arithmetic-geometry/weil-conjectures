/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite intermediate models of integral algebras at a finite prime fibre

Source: Stacks Project, More on Morphisms, Tag 0BSR,
`lemma-etale-makes-integral-split`, first proof, finite intermediate algebra;
fraction-numerator/denominator variant
(blueprint: lem-dl-a1-integral-finite-residue-model).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite intermediate algebra preserves the prime fibre and captures the prescribed
finite separable residue subfields. The residue fields are fraction fields of prime
quotients. Their embeddings are `Ideal.ResidueField.map`; the intermediate fields in the
conclusion are exactly the images of these embeddings, not independently chosen fields.

Source: Stacks Project, More on Morphisms, Tag 0BSR, first proof, finite intermediate algebra
(blueprint: lem-dl-a1-integral-finite-residue-model).

Proof plan:
1. Integral incomparability (`lem-weil-pbc-integral-incomparability`) gives, for each pair
   of distinct primes over p, an element in one prime but outside the other.
2. Choose a finite spanning family of each F over k
   (`def-weil-finite-dimensional-subspace`). Write each element as a quotient in D/r,
   and lift its numerator and its nonzero denominator to D.
3. Adjoin all these lifts and the pairwise separators to A. This is a finite set, and its
   elements are integral. By `lem-sc-finite-generated-integral-subring` its generated
   subalgebra C is module-finite. For the empty fibre use the empty generating set.
4. Every monic relation over A is a monic relation over C, so D is integral over C.
   The separators make the contractions of the original fibre primes pairwise distinct.
5. Integral injective lying over (`lem-weil-pbc-integral-injective-lying-over`) lifts every
   prime of C over p to a prime of D over p. Thus contraction is bijective, also when the
   original fibre is empty.
6. Inside E, take the k-span of the images of finite A-module generators of C. This span
   contains 1 and is closed under products, hence is a finite-dimensional domain algebra.
   By `lem-weil-pbc-finite-dimensional-domain-is-field` it is a field. It therefore equals
   the image L of the fraction field of C/(r ∩ C), proving finite-dimensionality of L/k.
7. The chosen numerator and denominator lifts put every spanning element of F in L,
   so F is contained in L. Every p-power witnessing pure inseparability over F also lies
   in L (`def-weil-pbc-finite-purely-inseparable-extension`). In characteristic zero,
   E = F forces L = E. Empty-fibre residue conclusions have no indices. -/
theorem exists_integral_finite_residue_model
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.IsIntegral A D] (p : Ideal A) [p.IsPrime]
    (hfibre : (p.primesOver D).Finite)
    (F : ∀ r : p.primesOver D,
      @IntermediateField p.ResidueField r.1.ResidueField _ _
        (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra)
    (hfinite : ∀ r, @FiniteDimensional p.ResidueField (F r) _ _
      (@Subalgebra.algebra _ _ _ _
        (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
        (@IntermediateField.toSubalgebra _ _ _ _
          (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
          (F r))).toModule)
    (hseparable : ∀ r, @Algebra.IsSeparable p.ResidueField (F r) _ _
      (@Subalgebra.algebra _ _ _ _
        (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
        (@IntermediateField.toSubalgebra _ _ _ _
          (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra (F r))))
    (hpure : ∀ r, IsPurelyInseparable (F r) r.1.ResidueField) :
    ∃ C : Subalgebra A D, Module.Finite A C ∧
      Set.BijOn (fun r : Ideal D ↦ r.comap C.val) (p.primesOver D) (p.primesOver C) ∧
      (∃ L : ∀ r : p.primesOver D,
        @IntermediateField p.ResidueField r.1.ResidueField _ _
          (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra,
        ∀ r, (@IntermediateField.toSubfield _ _ _ _
          (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra (L r)) =
            (Ideal.ResidueField.map (r.1.comap C.val) r.1 C.val rfl).fieldRange ∧
          (@IntermediateField.toSubfield _ _ _ _
            (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra (F r)) ≤
          (@IntermediateField.toSubfield _ _ _ _
            (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra (L r)) ∧
          @FiniteDimensional p.ResidueField (L r) _ _
            (@Subalgebra.algebra _ _ _ _
              (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
              (@IntermediateField.toSubalgebra _ _ _ _
                (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
                (L r))).toModule ∧
          IsPurelyInseparable (L r) r.1.ResidueField) ∧
      Algebra.IsIntegral C D := by
  sorry

end Algebra
