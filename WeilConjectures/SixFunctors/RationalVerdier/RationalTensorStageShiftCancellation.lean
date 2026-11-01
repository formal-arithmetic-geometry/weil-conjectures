/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalTensorOppositeShift
public import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence

/-! # Opposite tensor shifts commute with finite scalar extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage stageSystem)

attribute [local irreducible] ScalarLocalization.category rationalDerivedTensor
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage

/-- The fixed scalar tensor comparison preserves cancellation of opposite shifts.
This assertion involves tensor and scalar extension only, with no duality datum.
Source: blueprint thm-coef-qbar-verdier steps 3--4, finite coefficient transport;
Stacks Tags 07A4, 08J9 and 0941.
(blueprint: lem-coef-rational-tensor-stage-shift-cancellation-X3).

Proof: choose flat-term K-flat integral representatives for both operands and use
the same shifted representatives over the larger coefficient ring. The recorded
scalar shifts are the descents of the termwise shifts. The integral right-slot
and left-slot normalization predicates identify tensor cancellation with the
signed reindexing on each finite-level total-tensor summand. The normalization
of scalarTensorOrdinary identifies the scalar tensor map with scalar balancing
on those summands. Balancing commutes with both reindexings; both routes have
the same Koszul signs. These equalities also commute with coefficient transitions.
Take products and the fixed cone of one minus transition, using the diagonal
Roos shift coefficients. The normalized scalar completion comparison then
identifies the resulting square with the completed integral one. Restrict to
constructible objects and localize scalars. Full faithfulness of precomposition
by binary localization proves the rational square. Finally transport it along
operationStageTransitionIso, which commutes with the recorded stage shifts;
rationalTensorStageComparison is conjugated by this same isomorphism in both
slots. Multiplying by the common integer unit (-1)^(n(n-1)/2), and additivity of
scalar extension, gives the displayed signed square. This proof applies also
to n=0, negative n, and identity coefficient extensions. -/
theorem signedOppositeShift_scalar {E L : Index l Ω} (h : E ≤ L)
    (n : ℤ) (K P : Stage l Ω X E) :
    letI := units D l hl X
    let T := (stageSystem l Ω X).T h
    letI : T.CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
    (tensor D l hl X (Coefficient.{u} l Ω L)).map
        (Prod.mkHom ((T.commShiftIso (-n)).hom.app K)
          ((T.commShiftIso n).hom.app P)) ≫
      signedOppositeShift D l hl X (Coefficient.{u} l Ω L) (T.obj K) (T.obj P) n ≫
        (rationalTensorStageComparison l Ω X h).inv.app (K, P) =
      (rationalTensorStageComparison l Ω X h).inv.app (K⟦-n⟧, P⟦n⟧) ≫
        T.map (signedOppositeShift D l hl X (Coefficient.{u} l Ω E) K P n) := by sorry

end WeilConjectures.RationalVerdier
