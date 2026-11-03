/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange

import all WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorConstructibility

/-! # Native ordinary integral tensor closure

The proof compares native constructible homology with the existing integral
constant-model predicate. (blueprint: lem-sf-native-integral-tensor-closure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures

set_option maxHeartbeats 100000 in
-- The comparison proof expands degreewise homology predicates.
-- Native derived-category endpoint checking needs additional heartbeats.
/-- Ordinary integral tensor preserves the native bounded constructible predicate.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-int-tensor/
det-lem-int-tensor-product.proof.md, reduction to a stratum and the stratum.
(blueprint: lem-sf-native-integral-tensor-closure).

Proof: finite type over a field makes X Noetherian. For each homology degree, use
integerConstructibleComparison to identify the native constructible-module condition
with the constant-model condition. The boundedness clause is unchanged. Transport
both input hypotheses to constant models, apply integralTensorConstructibility, then
transport the result back. No finite-Tor hypothesis is needed; the zero complex and
empty scheme satisfy the same equivalence.
-/
theorem nativeIntegralTensorClosure
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ l)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (K L : D (properOpenIntegralCoefficient l E) X)
    (hK : boundedConstructible (condensedRingObj (properOpenIntegralCoefficient l E) X) K)
    (hL : boundedConstructible (condensedRingObj (properOpenIntegralCoefficient l E) X) L) :
    boundedConstructible (condensedRingObj (properOpenIntegralCoefficient l E) X) (K ⊗ L) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have hcmp (N : D (properOpenIntegralCoefficient l E) X) :
      boundedConstructible (condensedRingObj (properOpenIntegralCoefficient l E) X) N ↔
        constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X N :=
    and_congr Iff.rfl (forall_congr' fun n ↦ integerConstructibleComparison.{u} l E X _)
  exact (hcmp _).mpr (integralTensorConstructibility.{u} l E k p hp hpl X K L
    ((hcmp K).mp hK) ((hcmp L).mp hL))

end WeilConjectures
