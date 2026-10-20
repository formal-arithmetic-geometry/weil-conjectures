/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.CompletedProjectionData
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Normalized tensor projection mates after finite coefficient reduction -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.AdicSites

variable {Y X : Site.{u}} {A : Type u} [CommRing A] {I : Ideal A}

namespace ProjectionCoherence

/-- The canonical finite scalar tensor presentations and the evaluation identity for
projection mates. This construction does not require perfect quotient coefficients.

Source: Stacks, Cohomology on Sites, Tags 07A4, 0B56, 0E48 and 0941; completed
projection coherence, proof Steps 3, 6, 8 and 9
(blueprint: lem-pur-finite-quotient-tensor-projection).

Proof: At each coefficient ring A/I^(n+1), choose a derived tensor with its genuine
K-flat tensor model, using the closed symmetric monoidal derived tensor theorem.
Present the geometric pullback by the actual module inverse image and the exact
localized pullback; its tensor comparison is the canonical comparison on K-flat
representatives. Present each scalar extension by the identity geometric morphism
and the actual quotient homomorphism. The universal left-derived comparison for
extend supplies its epsilon; the normalized finite module and derived adjunctions
supply its right adjoints. Canonical derived tensor pullback provides balancing,
so these data form FiniteTensor and satisfy its two normalization equations.
Form the ringed coefficient square, with the ordinary module comparison fixed
on the insertion m mapped to 1 tensor m. Its derived comparison is finitePullIso
by the existing K-flat normalization and uniqueness. Ringed exchange/tensor
coherence applied to H and K says that reducing the ordinary tensor projection
and then the coefficient exchange equals the finite tensor projection after the
source coefficient exchange and the scalar balancing. Evaluation of the strict
reduction tower gives precisely this coefficient exchange: check the two
adjuncts on a common K-flat representative, using the prescribed evaluation,
finite adjunction and finiteRestrictionPushIso normalizations. Combine these
two equalities to obtain FiniteEquation, with its displayed order of comparisons.
Everything is done on the strict diagram before evaluation or inverse limit;
no faithfulness assertion about reduction or evaluation is required. -/
theorem finiteQuotientTensorProjection [IsNoetherianRing A]
    (f : Morphism Y X) (o : TensorData f A) :
    ∃ s : ∀ n : ℕ, FiniteTensor (I := I) o n, o.FiniteEquation s := by
  sorry

end ProjectionCoherence
end CategoryTheory.AdicSites
