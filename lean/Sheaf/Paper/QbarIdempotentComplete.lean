/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.RationalizationKaroubi
import Sheaf.Paper.RationalizationIdempotentComplete
public import WeilConjectures.CategoryTheory.Idempotents.Triangulated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Idempotents.Karoubi
import Sheaf.Paper.SfRationalizationKaroubi

/-!
# Idempotent completeness of the common-stage coefficient category

Source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/
`lem-weil-qbar-idempotent-complete.md` (blueprint: lem-weil-qbar-idempotent-complete).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Idempotents AlgebraicGeometry

namespace WeilConjectures

/-- The finite-stage common coefficient category is idempotent complete, and its canonical
Karoubi inclusion is an exact equivalence.

Source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/
`lem-weil-qbar-idempotent-complete.md`, node order 2115
(blueprint: lem-weil-qbar-idempotent-complete).

Proof: (1) For every finite coefficient field in the chosen algebraic closure, apply
`lem-weil-rationalization-idempotent-complete` to the fixed finite-field datum, the prime
with `l ≠ D.p`, and the finite-type `k`-scheme `Y`; these are exactly the stages of
`def-weil-algebraically-closed-coefficients`. (2) Represent an idempotent at a finite
stage and enlarge to a common finite field where its equation is witnessed; transport
both the representative and its square along scalar extension, so the transported map
is idempotent. (3) Apply the finite-stage splitting theorem at that enlarged field and
represent the splitting arrows in the common-stage category; their composites are the
identity and the original idempotent. (4) The common-stage category is triangulated and
additive, while `lem-weil-karoubi-envelope-fully-faithful` gives full faithfulness of the
canonical inclusion. The splitting makes every envelope object isomorphic to one in the
image. (5) The explicit splitting quasi-inverse is an equivalence by the envelope
composition laws. (6) `lem-weil-karoubi-envelope-triangulated` supplies the retract
triangulation and exactness of the canonical inclusion, yielding the exact equivalence.
-/
theorem qbar_idempotent_complete
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar]
    (Y : AlgebraicGeometry.Scheme.{u}) [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))] :
    IsIdempotentComplete (generalAlgebraicallyClosedConstructibleCategory l Qbar Y) ∧
      (toKaroubi (generalAlgebraicallyClosedConstructibleCategory l Qbar Y)).IsEquivalence ∧
        (toKaroubi (generalAlgebraicallyClosedConstructibleCategory l Qbar Y)).IsTriangulated := by
  sorry

end WeilConjectures
