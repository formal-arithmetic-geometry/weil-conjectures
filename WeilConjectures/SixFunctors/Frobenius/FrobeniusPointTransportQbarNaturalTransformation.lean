/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Frobenius.FrobeniusPointTransport

/-! # Common-stage natural transformation for Frobenius transport

Source: Deligne, Weil II (1.1.7), pp. 150--151; the explicit common-stage descent
is the argument of lem-weil-point-rational-family-common-stage-naturality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The stage-represented Frobenius components form a natural transformation.
Source: Deligne, Weil II (1.1.7), pp. 150--151; coefficient-descent part of
lem-weil-frobenius-point-transport-natural and the existing common-stage family theorem.
(blueprint: lem-weil-frobenius-point-transport-qbar-natural-transformation).

Proof: at each finite coefficient field, rationalize the integral natural transformation
formed by restriction followed by the specified comparison kappa. The pure-tensor
formulas for rational fibre and pullback give naturality for every rational morphism.
The rational coefficient square gives compatibility under every field inclusion.
Apply rational_family_common_stage_naturality to this family. The unit and tower
hypotheses are the corresponding clauses of PointCompositeComparison.tower_and_actions;
its representative-action and enlargement clauses give the other hypotheses. The
component formula of the descent theorem is the image of the rational component at
the object's own stage under coefficient extension by Shrink.algEquiv and the fixed
stage functor. This is exactly frobeniusPointTransportQbar. Retain the canonical
object equalities at the rational, coefficient and stage functors to obtain HEq.
The argument includes the zero object and identity field extension. No choice of an
arbitrary witness is used: the existing descent theorem determines the transformation
on every component by its displayed stage formula. -/
theorem frobeniusPointTransportQbar_naturalTransformation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    letI := frobeniusPointPrimeInvertible D l hl
    ∃ τ : pointQbarFibre D l hl Ω ⟶
        commonStageDerivedPullback l Ω (frobeniusPointIso D).hom ⋙
          pointQbarFibre D l hl Ω,
      ∀ A, HEq (τ.app A) (frobeniusPointTransportQbar D l hl Ω A) := by
  sorry

end WeilConjectures
