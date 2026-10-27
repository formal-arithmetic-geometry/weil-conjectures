/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W7
-/
module

public import Sheaf.Paper.SystemTensorPresentationData

/-! # A step of strict-system presentation comparison

Source: Stacks 03EL, 07A4 and 0B56; the explicit presentation argument.
(blueprint: lem-pur-system-tensor-semilinear-realization).
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

/-- Realize the supplied semilinear calculus by normalized diagram operations.
Source: Zheng 4.1 and 4.10; Stacks 03DI, 03EL, 07A4, 0B56 and 0E8I;
presentation comparison Steps 1--7 and the source-realization paragraph
(blueprint: lem-pur-system-tensor-semilinear-realization).

Proof: retain the system calculus a W on each scheme. Use the sectionwise
constant-coefficient pullback and extension operations on the vertical sequence
site. The constant-section map identifies the coefficients of each supplied
geometric inverse image with the fixed quotient coefficients; its normalization
is the set-sheaf adjunction unit, and naturality gives compatibility with every
quotient transition. Restriction along the inverse ring isomorphism is an exact
module equivalence. Its ordinary tensor map is identity on pure tensors;
total K-flat descent gives the normalized target tensor comparison. Compare
pullbacks and pushforwards by the ordinary adjunction and then derive using
system K-injectives. The source tensor comparison uses a W's own tensor models.
Their signed summand equations and cochain rigidity identify geometric mu.
Substitution in its counit-defined mate gives the geometric projection equation.
For an open, use the pro-etale slice equivalence, which retains all sections,
morphisms and horizontal transitions. The left-adjoint comparison of extension
with the localization supplied by a is uniquely fixed by the ordinary unit;
this gives the localization part. These constructions give TensorOperations
with systems exactly a W.systems and both requested comparisons. No comparison
with a second arbitrary tensor package, and no universe lift, is required. -/
theorem semilinearPresentation_realization
    (a : ∀ W : Scheme.{u}, PresentationSections (l := l) (E := E) W) :
    ∃ o : TensorOperations l E, Nonempty (SemilinearPresentationComparison a o) := by
  sorry

end WeilConjectures.SystemTensorMate
