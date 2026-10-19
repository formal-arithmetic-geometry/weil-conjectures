/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.RingTheory.CompleteIntersectionLocal
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.TraceFormula.EssentiallyFiniteTypeCIKernelInvariance
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import Sheaf.RingTheory.LciConormalFreeRankCodimension
import Sheaf.RingTheory.ConormalGeneratorsGlobalCompleteIntersection
import Sheaf.RingTheory.LCIRegularSequenceGlobalCompleteIntersection
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Extension.Presentation.Basic
import Sheaf.SixFunctors.TraceFormula.LciConormalFibreFieldChange
import Sheaf.TraceFormula.LciPointwiseCriterion

/-!
# Complete-intersection local rings under extension of the base field

Source: Stacks Project, Algebra, Lemma 10.135.10, Tag 00SI
(blueprint: lem-trf-lci-field-change-local).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Complete-intersection local rings at corresponding primes are invariant under any
extension of the base field. The contraction uses `c ↦ 1 ⊗ c`, and the tensor product
has its canonical left-factor `K`-algebra structure. No separability, algebraicity, or
completeness assumption is imposed.

Source: Stacks Project, Algebra, Lemma 10.135.10, Tag 00SI
(blueprint: lem-trf-lci-field-change-local).

Proof:
1. Choose a finite polynomial presentation `P → C` with kernel `I`, using
   def-weil-pbc-finite-type-algebra and def-weil-pbc-mv-polynomial-ring.
   lem-weil-pbc-presentation-base-change gives `K ⊗ C = P_K / I_K`; pull back both primes.
2. lem-weil-pbc-dimension-at-point-field-extension identifies the topological dimensions
   at the corresponding points, giving the same integer `d` and codimension `n - d`.
3. lem-trf-lci-conormal-fibre-field-change identifies the conormal fibre after extension
   of its residue field with the conormal fibre of the extended presentation. This
   follows by flat exactness on `I² ⊆ I ⊆ P`, localization, and tensor associativity;
   in particular the finite vector-space dimensions agree.
4. Suppose `C_q` is a complete intersection. Its defining regular-local presentation
   and the polynomial local presentation have regular-sequence kernels simultaneously
   by lem-trf-essentially-finite-type-ci-kernel-invariance; polynomial local rings are
   regular by lem-weil-pbc-polynomial-ring-field-regular-ring. Then
   lem-weil-pbc-lci-regular-sequence-global-complete-intersection spreads this to a
   principal neighbourhood of `q`.
5. lem-weil-pbc-lci-conormal-free-rank-codimension gives conormal rank `n - d` there.
   Steps 2 and 3 give the same fibre dimension at the extended prime.
6. Noetherianity of the polynomial ring makes the conormal module finite. Apply
   lem-weil-pbc-nakayama-local-generators to lift a residue-field basis to `n - d`
   generators, and lem-weil-pbc-lci-conormal-generators-global-complete-intersection to
   get a principal global-complete-intersection neighbourhood over `K`.
   lem-trf-lci-pointwise-criterion gives the required local-ring property.
7. Conversely start with the extended local ring. Apply steps 4 and 5 over `K`, descend
   the conormal fibre dimension by step 3, and use Nakayama and the same generator
   criterion over `k`. The pointwise criterion gives the complete-intersection property
   of `C_q`. Empty regular sequences are retained in both directions. -/
theorem isCompleteIntersectionLocal_fieldChange
    (k : Type u) (K : Type v) (C : Type w)
    [Field k] [Field K] [CommRing C] [Algebra k K] [Algebra k C]
    [FiniteType k C] (qK : Ideal (K ⊗[k] C)) [qK.IsPrime] :
    IsCompleteIntersectionLocal k
        (Localization.AtPrime
          (qK.comap (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom)) ↔
      IsCompleteIntersectionLocal K (Localization.AtPrime qK) := by
  sorry

end Algebra
