/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.CanonicalIntegralLeftRealization
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
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

/-- Compatibility of the supplied left realization with the finite-Tor realization.
Source: `CoefficientConstructionRing.integralLeft_normalized`, by cancellation of
its canonical compact-support realization isomorphism.
(blueprint: lem-sf-canonical-integral-left-compatible). -/
theorem canonicalIntegralLeft_compatible
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (E : FieldStage.{max u v} l) (c : Compactification f) :
      ∃ η : canonicalIntegralOperation l Ω D hl R E c ⋙
          PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
        PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
          sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier,
        ∀ K : finiteTorConstructibleIntegralCategory l E.carrier X,
          (canonicalIntegralLeft l Ω D hl R E c).hom.app K =
            (sfIntegralConstructible l E.carrier Y).ι.map (η.hom.app K) ≫
              (sfQcqsCompactSupportRealization l E.carrier D.k
                (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
                  ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K) := by
  unfold canonicalIntegralOperation
  refine ⟨R.integralLeft c E, ?_⟩
  intro K
  unfold canonicalIntegralLeft
  exact (Iso.eq_comp_inv ((sfQcqsCompactSupportRealization l E.carrier D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) c).app
      ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K))).mpr
        (R.integralLeft_normalized c E K).symm
end WeilConjectures.ConstructibleExceptionalCoefficients
