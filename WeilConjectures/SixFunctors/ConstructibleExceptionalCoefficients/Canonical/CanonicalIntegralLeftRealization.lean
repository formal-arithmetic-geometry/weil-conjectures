/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.CanonicalIntegralOperation
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge

/-! # Canonical typing of the supplied integral left realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The existing realization, with the canonical integral derived categories explicit.
This is the supplied isomorphism itself; no object is selected from an existence theorem.
Source: the integral branch of `CoefficientConstructionRing.left`.
(blueprint: def-sf-canonical-integral-left-realization). -/
@[irreducible] def canonicalIntegralLeft
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (E : FieldStage.{max u v} l) (c : Compactification f) :
    canonicalIntegralOperation l Ω D hl R E c ⋙ (finiteTorConstructibleIntegral l E.carrier Y).ι ≅
      (finiteTorConstructibleIntegral l E.carrier X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c :=
  by
    unfold canonicalIntegralOperation
    exact R.left c (.integral E)

end WeilConjectures.ConstructibleExceptionalCoefficients
