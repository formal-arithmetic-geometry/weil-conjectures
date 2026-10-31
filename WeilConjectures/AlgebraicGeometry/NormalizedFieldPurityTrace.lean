/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedFieldPurityTraceCommonStage
import WeilConjectures.AlgebraicGeometry.AdicPurityScalarNaturality
import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonIdentification
import WeilConjectures.AlgebraicGeometry.RationalLatticeAdicDomain
import WeilConjectures.AlgebraicGeometry.PbcRationalTransport
import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
import WeilConjectures.SixFunctors.RationalOperations
import WeilConjectures.AlgebraicGeometry.PbcDescentFunctors
import WeilConjectures.AlgebraicGeometry.CommonStageSmoothOperationIdentification
import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison

/-! # Normalized field purity, inverse orientation and counit trace

Source: current blueprint, prop-functor-package.proof.md clause (6),
and smooth-purity transport Steps 1--2
(blueprint: lem-sf-normalized-field-purity-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 128

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.NormalizedFieldPurityTrace

variable (P : PurityFiniteSetting.{u})
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (r : ℕ) [SmoothOfRelativeDimension r f]
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))

attribute [local instance] sourcePrimeInvertible targetPrimeInvertible

attribute [local irreducible] RationalSmoothPurityCanonical.rationalSource
  RationalSmoothPurityCanonical.commonSource sfRationalScalarExtension
  RationalSmoothPurityCanonical.sourceScalar
  RationalSmoothPurityCanonical.rationalIso RationalSmoothPurityCanonical.smallModelIso
  RationalSmoothPurityCanonical.commonIso RationalSmoothPurityCanonical.commonSourceComparison
  commonSourceComparison

attribute [local irreducible] commonSourceScalar

/-- The complete field-purity conclusions in the specified coefficient presentations.
The integral family is supplied, rather than chosen from an unconstrained existence.
Source: clause (6), rationalization, finite extensions and common finite stages
(blueprint: lem-sf-normalized-field-purity-trace). -/
structure Conclusion
    (A : AdicPurityScalarNaturality.Data P.field P.coefficients f r S) where
  localization (E : AdicPurityScalarNaturality.Field P.field P.coefficients) :
    AdicPurityScalarNaturality.source P.field P.coefficients f r E ⋙
        RationalScalarComparisonIdentification.Q P.field P.coefficients E X ≅
      RationalScalarComparisonIdentification.Q P.field P.coefficients E Y ⋙
        RationalScalarComparisonIdentification.H P.field P.coefficients f r E
  localization_normalized (E : AdicPurityScalarNaturality.Field P.field P.coefficients) :
    RationalScalarComparisonIdentification.SourceLocalizationNormalization
      P.field P.coefficients f r E (localization E)
  rationalizes (E : AdicPurityScalarNaturality.Field P.field P.coefficients) :
    PassageEquations (AdicPurityScalarNaturality.operation P.field P.coefficients f S E).adjunction
      (RationalScalarComparisonIdentification.O P.field P.coefficients f S E).adjunction
      (RationalScalarComparisonIdentification.Q P.field P.coefficients E X)
      (RationalScalarComparisonIdentification.Q P.field P.coefficients E Y)
      (fun K ↦ (A.gamma E).app K) (rationalGamma P f r S E)
      (fun K ↦ (localization E).app K)
      (fun K ↦ (RationalScalarComparisonIdentification.gLocalization
        P.field P.coefficients f S E).app K)
      (fun M ↦ (S.fields.rationalizationComparison
        (integralExceptionalCompactification P.field f)
        (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)).q.app M)
  rational_natural (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
      {K L : RationalScalarComparisonIdentification.RCat P.field P.coefficients E Y}
      (v : K ⟶ L) :
    (RationalScalarComparisonIdentification.H P.field P.coefficients f r E).map v ≫
        (rationalGamma P f r S E L).hom =
      (rationalGamma P f r S E K).hom ≫
        (RationalScalarComparisonIdentification.G P.field P.coefficients f S E).map v
  a (E F : AdicPurityScalarNaturality.Field P.field P.coefficients) (h : E ≤ F) :
    RationalScalarComparisonIdentification.H P.field P.coefficients f r E ⋙
        RationalScalarComparisonIdentification.T P.field P.coefficients E F h X ≅
      RationalScalarComparisonIdentification.T P.field P.coefficients E F h Y ⋙
        RationalScalarComparisonIdentification.H P.field P.coefficients f r F
  a_canonical (E F : AdicPurityScalarNaturality.Field P.field P.coefficients) (h : E ≤ F)
      (K : RationalScalarComparisonIdentification.RCat P.field P.coefficients E Y) :
    (a E F h).app K = RationalSmoothPurityCanonical.sourceScalar P.coefficients.l
      E.val F.val (IntermediateField.inclusion h) f r K
  extension (E F : AdicPurityScalarNaturality.Field P.field P.coefficients) (h : E ≤ F) :
    PassageEquations
      (RationalScalarComparisonIdentification.O P.field P.coefficients f S E).adjunction
      (RationalScalarComparisonIdentification.O P.field P.coefficients f S F).adjunction
      (RationalScalarComparisonIdentification.T P.field P.coefficients E F h X)
      (RationalScalarComparisonIdentification.T P.field P.coefficients E F h Y)
      (rationalGamma P f r S E) (rationalGamma P f r S F)
      (fun K ↦ (a E F h).app K)
      (fun K ↦ (RationalScalarComparisonIdentification.b
        P.field P.coefficients f S E F h).app K)
      (fun M ↦ (RationalScalarComparisonIdentification.c
        P.field P.coefficients f S E F h).app M)
  source_unit (E : AdicPurityScalarNaturality.Field P.field P.coefficients) :
    RationalScalarComparisonIdentification.UnitEquation (a E E le_rfl)
      (RationalScalarComparisonIdentification.unit P.field P.coefficients E X)
      (RationalScalarComparisonIdentification.unit P.field P.coefficients E Y)
  source_composite (E F L : AdicPurityScalarNaturality.Field P.field P.coefficients)
      (h : E ≤ F) (k : F ≤ L) :
    RationalScalarComparisonIdentification.CompositionEquation
      (a E F h) (a F L k) (a E L (h.trans k))
      (RationalScalarComparisonIdentification.alpha P.field P.coefficients E F L h k X)
      (RationalScalarComparisonIdentification.alpha P.field P.coefficients E F L h k Y)
  exceptional_unit (E : AdicPurityScalarNaturality.Field P.field P.coefficients) :
    RationalScalarComparisonIdentification.UnitEquation
      (RationalScalarComparisonIdentification.b P.field P.coefficients f S E E le_rfl)
      (RationalScalarComparisonIdentification.unit P.field P.coefficients E X)
      (RationalScalarComparisonIdentification.unit P.field P.coefficients E Y)
  exceptional_composite (E F L : AdicPurityScalarNaturality.Field P.field P.coefficients)
      (h : E ≤ F) (k : F ≤ L) :
    RationalScalarComparisonIdentification.CompositionEquation
      (RationalScalarComparisonIdentification.b P.field P.coefficients f S E F h)
      (RationalScalarComparisonIdentification.b P.field P.coefficients f S F L k)
      (RationalScalarComparisonIdentification.b P.field P.coefficients f S E L (h.trans k))
      (RationalScalarComparisonIdentification.alpha P.field P.coefficients E F L h k X)
      (RationalScalarComparisonIdentification.alpha P.field P.coefficients E F L h k Y)
  support_unit (E : AdicPurityScalarNaturality.Field P.field P.coefficients) :
    RationalScalarComparisonIdentification.UnitEquation
      (RationalScalarComparisonIdentification.c P.field P.coefficients f S E E le_rfl)
      (RationalScalarComparisonIdentification.unit P.field P.coefficients E Y)
      (RationalScalarComparisonIdentification.unit P.field P.coefficients E X)
  support_composite (E F L : AdicPurityScalarNaturality.Field P.field P.coefficients)
      (h : E ≤ F) (k : F ≤ L) :
    RationalScalarComparisonIdentification.CompositionEquation
      (RationalScalarComparisonIdentification.c P.field P.coefficients f S E F h)
      (RationalScalarComparisonIdentification.c P.field P.coefficients f S F L k)
      (RationalScalarComparisonIdentification.c P.field P.coefficients f S E L (h.trans k))
      (RationalScalarComparisonIdentification.alpha P.field P.coefficients E F L h k Y)
      (RationalScalarComparisonIdentification.alpha P.field P.coefficients E F L h k X)
  closed_natural {K L : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Y} (v : K ⟶ L) :
    (RationalSmoothPurityCanonical.commonSource P.coefficients.l P.coefficients.Qbar f r).map v ≫
        (closedGamma P f r S L).hom =
      (closedGamma P f r S K).hom ≫ (closedOperation P f S).G.map v
  descends (E : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar) :
    PassageEquations (smallOperation P f S E).adjunction (closedOperation P f S).adjunction
      (ConstructibleExceptionalCoefficients.commonInclusion
        P.coefficients.l P.coefficients.Qbar X E)
      (ConstructibleExceptionalCoefficients.commonInclusion
        P.coefficients.l P.coefficients.Qbar Y E)
      (smallGamma P f r S E) (closedGamma P f r S)
      (commonSourceComparison P f r E)
      (fun K ↦ (S.common.commonComparison
        (integralExceptionalCompactification P.field f) E).b.app K)
      (fun M ↦ (S.common.commonComparison
        (integralExceptionalCompactification P.field f) E).q.app M)

  common_source_composite : CommonSourceComposition P f r
  common_check (side : Bool) (m : ℕ)
      (K L : Fin m → generalAlgebraicallyClosedConstructibleCategory
        P.coefficients.l P.coefficients.Qbar
        (ConstructibleExceptionalCoefficients.endpoint X Y side))
      (v w : ∀ i : Fin m, K i ⟶ L i) :
    (∀ i : Fin m, v i = w i) ↔
      ∃ (E : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
        (hK : ∀ i : Fin m, (K i).stage ≤ E) (hL : ∀ i : Fin m, (L i).stage ≤ E)
        (vE wE : ∀ i : Fin m, (K i).toStage (hK i) ⟶ (L i).toStage (hL i)),
        (∀ i : Fin m, StageSystem.PairCategory.mkHom E (hK i) (hL i) (vE i) = v i ∧
          StageSystem.PairCategory.mkHom E (hK i) (hL i) (wE i) = w i) ∧
        ∀ i : Fin m, vE i = wE i

/-- The chosen normalized integral family gives the canonical field purity, its inverse
and its actual counit trace, with the three coefficient equations and their cocycles.
Source: current blueprint prop-functor-package.proof.md clause (6), and
thm-pur-rational-and-qbar-purity.proof.md Steps 1--2
(blueprint: lem-sf-normalized-field-purity-trace).

Proof:
1. By lem-pur-rational-lattice-adic-domain, every integral representative is derived
complete and has a single finite Tor interval at all levels. Use the simultaneous
family of lem-pur-adic-purity-scalar-naturality with its specified finite reductions.
2. Localize the exact linear functors, their natural transformations and the
exceptional Hom adjunction by prop-weil-pbc-rational-transport. The normalized
source localization and exceptional mate of
lem-pur-rational-scalar-comparison-identification identify the actual maps, not
just their objects. The canonical field components of thm-pur-rational-and-qbar-purity
are the images of these lattice components. lem-coef-rational-operations preserves
exceptional counits. This gives the forward purity and counit squares.
3. Apply the coefficient functor to both inverse identities and cancel the two
purity isomorphisms in the forward square. This proves the stated inverse equation.
4. Expand t as P(gamma) followed by epsilon. Substitute the counit square, use
naturality of c at gamma and then the purity square. Functoriality gives precisely
c at H(K), then P'(a), then t' at C_Y(K).
5. The a and b identity and composition equations are those of the normalized
localized comparison theorem. For c use the specified integral compact-support
comparison of lem-pur-compact-support-integral-coefficient-comparison and localize
its tensor-unitor and tensor-associator equations. Substitution into the inverse
and trace equations, followed by naturality, gives their identity/composite laws.
6. Apply prop-weil-pbc-descent-functors. The actual operation identification of
lem-pur-common-stage-smooth-operation-identification preserves the component
presentations and counits. Each common object has its literal finite-stage model;
smallModelIso retains the canonical algebra equivalence, so the same calculation
proves the three equations for every stage inclusion and every representative.
7. Any finitely many arrows admit representatives in one common finite field by
def-weil-algebraically-closed-coefficients. Equality is equality after further
extension, so the coefficient cocycles give independence of representatives and
all enlargement comparisons. No reduction from a field to a finite quotient occurs. -/
theorem normalizedFieldPurityTrace
    (A : AdicPurityScalarNaturality.Data P.field P.coefficients f r S) :
    Nonempty (Conclusion P f r S A) := by
  sorry

end WeilConjectures.NormalizedFieldPurityTrace
