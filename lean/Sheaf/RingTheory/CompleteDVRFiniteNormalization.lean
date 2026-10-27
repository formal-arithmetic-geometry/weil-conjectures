/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import WeilConjectures.AlgebraicGeometry.Regular

/-! # Finite normalization of a complete discrete valuation ring

Source: Stacks Project, More on Algebra, Tags 09EM (assertions (1), (4), (8)) and
09F8 (first paragraph of the proof); Algebra, Tag 032W.
(blueprint: lem-per-complete-dvr-finite-normalization)
-/

@[expose] public section

universe u v w

namespace IsDiscreteValuationRing

/-- The integral closure of a complete DVR in any finite extension of its fraction field
is a finite complete DVR with that fraction field, and is the unique DVR in that field
containing and dominating the original ring. No separability or residue-perfectness is needed.

Source: Stacks Project, More on Algebra, Tags 09EM and 09F8 (proof, first paragraph);
Algebra, Tags 032W, 0325, 00OK and 00PD.
(blueprint: lem-per-complete-dvr-finite-normalization)

Proof:
1. A DVR is a PID, hence Noetherian by lem-weil-pbc-pid-noetherian-normal.
   By lem-weil-pbc-complete-local-nagata it is Nagata. Applying def-weil-pbc-nagata-ring
   to the zero prime gives the N-2 property of def-weil-pbc-japanese-domain, which gives
   module finiteness of the integral closure for this possibly inseparable extension.
2. By lem-weil-pbc-integral-closure-finite-extension-normal, the integral closure C is
   a normal domain with fraction field L. The inclusion A into C is injective and integral,
   by def-weil-pbc-integral-closure and the embeddings into L.
3. By lem-weil-pbc-finite-over-complete-local-product and its domain clause, C is
   Noetherian and local and complete for its maximal ideal. By
   lem-weil-pbc-finite-algebra-local-radical, this maximal ideal contracts to that of A.
4. By lem-sc-dvr-dimension-one, A has dimension one. By
   lem-weil-pbc-integral-injective-dimension-equal, C also has dimension one. Normality,
   Noetherianity and locality imply that C is a DVR by lem-sc-normal-dim1-dvr.
5. For a competing DVR V, lem-weil-pbc-pid-noetherian-normal gives integral closedness
   in L. Every element of C satisfies a monic polynomial over A, hence over V, so C ⊆ V.
6. Choose uniformizers pi of A and t of C using def-sc-discrete-valuation-ring.
   Locality and lem-weil-pbc-dvr-unit-times-uniformizer-power give pi = u * t^e with
   e ≥ 1. Since pi is a nonunit in V, t is a nonunit in V. Write any nonzero x in V
   as a/b with nonzero a,b in C, and write a = u_a * t^r and b = u_b * t^s by the
   same power decomposition. If r ≥ s, x belongs to C. If r < s, setting q = s-r ≥ 1
   gives t^(-1) = (u_a * u_b^(-1))^(-1) * x * t^(q-1) in V, a contradiction.
   Zero also belongs to C, proving V ⊆ C and hence V = C.
-/
theorem complete_finite_normalization
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Module.Finite K L] :
    ∃ hC : IsDiscreteValuationRing (integralClosure A L),
      IsFractionRing (integralClosure A L) L ∧
      Module.Finite A (integralClosure A L) ∧
      IsAdicComplete
        (@IsLocalRing.maximalIdeal (integralClosure A L) _ hC.toIsLocalRing)
        (integralClosure A L) ∧
      (@IsLocalRing.maximalIdeal (integralClosure A L) _ hC.toIsLocalRing).comap
        (algebraMap A (integralClosure A L)) = IsLocalRing.maximalIdeal A ∧
      ∀ (V : Subalgebra A L) [IsDiscreteValuationRing V],
        IsFractionRing V L →
        (IsLocalRing.maximalIdeal V).comap (algebraMap A V) = IsLocalRing.maximalIdeal A →
        V = integralClosure A L := by
  sorry

end IsDiscreteValuationRing
