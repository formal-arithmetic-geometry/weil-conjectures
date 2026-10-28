/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.Paper.AdicPurityScalarNaturality
public import Sheaf.Paper.SmoothTrace
public import Sheaf.Paper.FiniteReductionComparisons

/-! # Reduction of the specified integral exceptional counit

Source: six-operations package, clause (6), and purity transport.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.NormalizedIntegralPurityTrace
open AdicPurityScalarNaturality

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (r : ℕ) [SmoothOfRelativeDimension r f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (A : Data D C f r S) (E : Field D C)

set_option maxHeartbeats 800000 in
-- Elaborate the canonical coefficient comparisons with their full dependent endpoints.
/-- Reduction identifies the actual exceptional counit with the finite counit.
The target realization is the specified realization of the normalized adjoint system.
Source: six-operations package clause (6), exceptional counit equation; integral
exceptional adjunction and finite exceptional coefficient normalization
(blueprint: lem-sf-integral-purity-counit-reduction).

Proof: substitute the normalization equations for ε and c, then use
A.targetRealizationReductions to identify reduction of the inverse target
realization with the inverse of the prescribed exceptional mate. In the normalized
system S, the compact-support coefficient comparison and its exceptional mate satisfy
the counit equation. Map that equation through the full-category inclusions and
conjugate its scalar functors by their realization isomorphisms. Their naturality
cancels the intermediate realization maps. A.finiteRightNormalized identifies the
remaining finite exceptional realization with the ordinary etale adjoint, so its
counit is precisely smoothExceptionalCounit after the intrinsic equivalence.
The left realization S.ring.left gives the integral support term. On the finite
side, the same open and proper units identify it with finiteImageIso. Thus the
remaining composite is exactly c, followed by support of purAdicTargetReduction
and the finite exceptional counit. The finite-Tor hypothesis supplies boundedness
below, including the zero object and the empty scheme, so the totalized zero branch
of smoothExceptionalCounit is never used on a nonzero unbounded input.
-/
theorem integralPurityCounitReduction (K : Cat D C E Y) (n : ℕ)
    (ε : (PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
      (integralExceptionalCompactification D f)).obj
        (purAdicTarget D C E.val f K.obj) ⟶ K.obj)
    (hε : ε = (PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
      (integralExceptionalCompactification D f)).map
        ((A.targetRealization E).inv.app K) ≫
    (S.ring.left (integralExceptionalCompactification D f)
      (.integral (fieldStage D C E))).inv.app ((target D C f S E).obj K) ≫
    (finiteTorConstructibleIntegral C.l E.val Y).ι.map
      ((operation D C f S E).adjunction.counit.app K))
    (c : ∀ (N : DerivedCategory (scalarReductionSource C.l E.val X)) (n : ℕ),
      (scalarReductionDerivedExtension C.l E.val Y n).obj
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
          (integralExceptionalCompactification D f)).obj N) ⟶
      ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).obj
        ((scalarReductionDerivedExtension C.l E.val X n).obj N))
    (hc : c = fun (N : DerivedCategory (scalarReductionSource C.l E.val X)) (n : ℕ) ↦
      (show (scalarReductionDerivedExtension C.l E.val Y n).obj
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
          (integralExceptionalCompactification D f)).obj N) ⟶
      ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).obj
        ((scalarReductionDerivedExtension C.l E.val X n).obj N) from
        (reductionBridge D C E Y n).hom.app _ ≫
  (PurCompactSupport.comparison.{u}
    (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n))
    (integralExceptionalCompactification D f)).app N ≫
  (PurCompactSupport.finiteImageIso.{u} C.l E.val n
    (integralExceptionalCompactification D f)).hom.app _ ≫
  ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).map
    ((reductionBridge D C E X n).inv.app N))) :
    (scalarReductionDerivedExtension C.l E.val Y n).map ε =
      c (purAdicTarget D C E.val f K.obj) n ≫
        ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).map
          (purAdicTargetReduction D C E.val f r K.obj K.property n) ≫
        (purAdicFiniteSetting D C E.val n).smoothExceptionalCounit f
          ((scalarReductionDerivedExtension C.l E.val Y n).obj K.obj) := by sorry

end WeilConjectures.NormalizedIntegralPurityTrace
