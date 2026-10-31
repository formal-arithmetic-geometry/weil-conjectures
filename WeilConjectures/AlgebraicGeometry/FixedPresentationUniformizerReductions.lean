/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerTracePurityComparisonData

/-! # Uniformizer reductions in a fixed normalized tower presentation

Source: purity transport Step 4, cofinal comparison with uniformizer powers.
(blueprint: lem-pur-fixed-presentation-uniformizer-reductions). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

-- Keep the canonical small-site sheafification instance ahead of generic alternatives.
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit

variable (P : PurityFiniteSetting.{u}) (M : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [QuasiSeparatedSpace Y]

/-- The exceptional comparison for a fixed normalized presentation has every positive
uniformizer reduction, and intertwines the actual tower purity with finite purity.
Source: latest blueprint, purity-transport Step 4 and tower-geometric-gamma (2).
(blueprint: lem-pur-fixed-presentation-uniformizer-reductions).

Proof: construct the exceptional comparison as the counit-preserving right-adjoint
comparison between the realized tower adjunction and the specified integral adjunction,
followed by the normalized completed exceptional comparison. Reduce its counit equation.
The normalized left comparison and FiniteNormalization.hom_normalized identify the
resulting finite comparison with finiteReduction: adjunction transposition determines
that comparison uniquely. For the purity equation first use ht to replace the tower
map by its trace transpose. The prescribed unit reductions hT identify its orientation
with the finite diagonal orientation. Reduction of the counit trace is therefore the
finite smooth trace, since the exceptional comparison preserves counits. Reduction
commutes with the inverse projection and with the tensor/unit source comparisons by
their K-flat normalization in T. Applying the finite adjunction Hom bijection now gives
the finite purity map. This gives the second equation at ell-power levels. Both hT
and ht are needed: an arbitrary source realization isomorphism is not fixed merely
by invertibility. Write ell as a unit times pi^e and restrict the uniformizer tower along e(n+1).
The arithmetic cofinal comparison preserves the reconstruction unit and counit and is
natural on whole tower maps. For each positive exponent m choose e(n+1) at least m;
quotient tensor reassociation gives both equations at m. Transition compatibility makes
them independent of this choice. Thus no faithfulness of separate derived evaluations
is invoked. Exponent one is included; d=0 uses the identity twist and shift, and on the
empty scheme both equations are equalities of the unique morphisms. -/
theorem fixed_presentation_uniformizer_reductions
    [SmoothOfRelativeDimension d (j ≫ p)]
    [IsNoetherian X] [IsNoetherian Y]
    [QuasiCompact (j ≫ p)] [IsSeparated (j ≫ p)] [LocallyOfFiniteType (j ≫ p)]
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
    [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
    (S : ConstructibleExceptionalCoefficients.RingSystem P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := j ≫ p))
    (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P M E j p d)
    (T : TowerTracePurityComparison.Stage P j p d S M E m)
    (hT : TowerTracePurityComparison.PrescribedUnitReductions P j p d S M E m T
      (TowerTracePurityComparison.orientation P j p d S M E m T))
    (ht : ∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y,
      TowerTracePurityComparison.tracePurity P j p d S M E m T
          (TowerTracePurityComparison.counitTrace P j p d S M E m T
            (TowerTracePurityComparison.orientation P j p d S M E m T)) K =
        TowerTracePurityComparison.tower P j p d S M E m T K) :
    ∃ e : ∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y,
        (((S.operation (SpTowerGamma.factorization j p)
          (.integral {carrier := E.val})).G.obj K).obj) ≅
          purAdicTarget P.field P.coefficients E.val (j ≫ p) K.obj,
      (∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) (n : ℕ),
        (scalarReductionDerivedExtension P.coefficients.l E.val X n).map (e K).hom ≫
            purAdicTargetReduction P.field P.coefficients E.val (j ≫ p) d
              K.obj K.property n =
          WeilConjectures.RealizedTowerPurity.finiteReduction P.field P.coefficients
            E.val (j ≫ p) S (SpTowerGamma.factorization j p) T.normal K n) ∧
      ∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) (n : ℕ),
        (scalarReductionDerivedExtension P.coefficients.l E.val X n).map
            (TowerTracePurityComparison.tower P j p d S M E m T K ≫
              (e K).hom) ≫
            purAdicTargetReduction P.field P.coefficients E.val (j ≫ p) d
              K.obj K.property n =
          purAdicSourceReduction P.field P.coefficients E.val (j ≫ p) d
            K.obj K.property n ≫
            (purAdicFiniteArrow P.field P.coefficients E.val (j ≫ p) d
              K.obj K.property n).hom := by sorry

end AlgebraicGeometry.ProEtale.TransportIntegralCounit
