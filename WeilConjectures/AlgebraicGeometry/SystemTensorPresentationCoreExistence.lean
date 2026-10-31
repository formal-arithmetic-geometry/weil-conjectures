/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemTensorPresentationData

/-! # A step of strict-system presentation comparison

Source: Stacks 03EL, 07A4 and 0B56; the explicit presentation argument.
(blueprint: lem-pur-system-tensor-presentation-core-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry
open WeilConjectures.SemilinearSections

namespace WeilConjectures.SystemTensorMate

variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Normalized tensor comparisons and adjunction/composition comparisons exist.
Source: Stacks 03EL, 07A4, 0B56; Steps 1--7 of the presentation comparison
(blueprint: lem-pur-system-tensor-presentation-core-existence).

Proof: the shared sequence-site presentation makes reindexing identity. Both
ordinary pullbacks are left adjoints to the same sectionwise direct image;
left-adjoint uniqueness fixes their comparison by the unit equation and gives
its counit equation. Compare open extensions by the corresponding conjugate
adjunction. Exact localization carries these comparisons to the derived
categories. On system K-injectives, the normalized derived units identify the
two derived adjunctions. The sectionwise direct-image compositor is the same
in both presentations; its conjugate therefore gives the composition equation.
The tensor comparison is induced by identity on ordinary pure tensors and signed
total summands. Exact monoidal K-flat descent and cochain model rigidity extend
this to a natural comparison with the displayed tensor_model normalization.
The ordinary inverse-image tensor comparison is uniquely its unit transpose
against the same laxTensor map. Thus its total-summand maps agree after the
pullback comparison. Cochain rigidity extends this equality to arbitrary
unbounded inputs and gives mu. No projection or open tensor mate comparison
is assumed: those are consequences of the displayed data. -/
theorem tensorPresentationCore_nonempty (o d : TensorOperations l E) :
    Nonempty (TensorPresentationCore o d) := by
  sorry

end WeilConjectures.SystemTensorMate
