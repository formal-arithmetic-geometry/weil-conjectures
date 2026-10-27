/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.RationalSmoothPurityCanonical
public import Sheaf.Paper.FieldShriekCompositionQcqs
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.SecSmoothPurity.RationalPurityCommonComparisons
import Sheaf.Paper.CanonicalTateComparisons

/-! # Rational purity: TraceCoherence

Source: current blueprint, rational purity trace and coherence construction.
Existing declarations are retained in this compilation subdivision.
(blueprint: prop-pur-rational-purity-trace-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open WeilConjectures

attribute [-instance] integralOperationsSiteSmall
  integralReductionSiteEssentiallySmall
attribute [local irreducible] IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  IntegralOnSlice.tower IntegralOnSlice.augmentation
  integralOperationsTensorTowerFunctor IntegralSystemRealization.tensorShifts

attribute [local irreducible] sfIntegralConstructible finiteTorConstructibleIntegral
  completedIntegralCoefficientSheafUnrestricted
  AlgebraicGeometry.Scheme.residueField
  PurCompactSupport.image sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  IntegralOnSlice.duality integralDerivedPullback integralCompletedTensor
  sfRationalScalarExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Iso.trans Iso.prod Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.leftAdjoint
attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom

namespace WeilConjectures.RationalPurityCoherence
open FrobeniusCoefficientTwists RationalSmoothPurityCanonical

attribute [local irreducible] integralSource integralTraceTranspose rationalSourceComparison
  smallModelIso rationalIso commonIso

attribute [local irreducible] rationalSource commonSource commonSourceComparison
  commonStageDerivedTensor completedIntegralCommRingSheafUnrestricted
attribute [local irreducible] commonStageDerivedPullback

section Trace
attribute [local irreducible] ScalarLocalization.category
attribute [local instance 3000] commonModelField commonModelAlgebra commonModelFinite
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
open ConstructibleExceptionalCoefficients
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The rational trace is the localization of the integral smooth trace, through
its actual source, support and representative comparisons. The integral trace is
already constructed from finite smooth trace and the projection formula.
Source: proof Steps 1--3 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def localizedSmoothTrace
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F.obj
      ((rationalSource P.coefficients.l P.extension f d).obj K) ⟶ K :=
  (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F.map
      (rationalSourceComparison P f d K).hom ≫
    (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).q.inv.app
      (integralSource P f d (representative P K)) ≫
    (rationalization P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) Y).map
        (integralTraceTranspose P f c S d (representative P K)) ≫
    (eqToIso (representative_eq P K)).hom

/-- The rational smooth trace in the small finite-field coefficient model: the
model purity map followed by the counit of the same support adjunction, i.e. the
adjoint transpose of the purity map.
Source: proof Steps 3 and 6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def modelSmoothTrace
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) Y) :
    (S.ring.operation c (.rational
      (commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).F.obj
          ((rationalSource P.coefficients.l
            (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
              (AdicSmoothDualizing.fieldIndex P)) f d).obj K) ⟶ K :=
  (S.ring.operation c (.rational
      (commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).F.map
    (smallModelIso P f c S d K).hom ≫
      (S.ring.operation c (.rational
        (commonField P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex P)))).adjunction.counit.app K

/-- The Qbar trace is the descended finite-stage trace: at a common-stage object of
finite stage i (written through the index of the stage setting, which is i itself),
the model trace at that literal finite field, included through the source comparison
and the support comparison q of that stage. It does not use the common-stage
exceptional functor, adjunction or purity map.
Source: proof Steps 3--6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def descendedSmoothTrace (i : Index P.coefficients.l P.coefficients.Qbar)
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex (stageSetting P i))) Y) :
    (operation P f c S .closed).F.obj
      ((commonSource P.coefficients.l P.coefficients.Qbar f d).obj
        ⟨AdicSmoothDualizing.fieldIndex (stageSetting P i), K⟩) ⟶
      ⟨AdicSmoothDualizing.fieldIndex (stageSetting P i), K⟩ :=
  (operation P f c S .closed).F.map
      (commonSourceComparison P.coefficients.l P.coefficients.Qbar f d
        ⟨AdicSmoothDualizing.fieldIndex (stageSetting P i), K⟩).hom ≫
    (S.common.commonComparison c (AdicSmoothDualizing.fieldIndex (stageSetting P i))).q.inv.app
      ((rationalSource P.coefficients.l
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex (stageSetting P i))) f d).obj K) ≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion
        (AdicSmoothDualizing.fieldIndex (stageSetting P i))).map
      (by
        have t := modelSmoothTrace (stageSetting P i) f c S d K
        dsimp only [stageSetting, AdicSmoothDualizing.fieldIndex,
          commonModelField, commonModelAlgebra, commonModelFinite] at t
        exact (commonCategory_eq P Y i) ▸ t)

/-- Existential presentation of the canonical rational and Qbar purity data, together
with the counit trace equations. Equality to the published trace-normalized maps
pins every witness; arbitrary rescalings of gamma or of the adjunction are excluded.
Source: proof Steps 1--6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def TraceClause : Prop :=
  (∃ G : sfRationalConstructibleCategory P.coefficients.l P.extension Y ⥤
        sfRationalConstructibleCategory P.coefficients.l P.extension X,
    ∃ adj : (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F ⊣ G,
    ∃ γ : ∀ K : sfRationalConstructibleCategory P.coefficients.l P.extension Y,
        (rationalSource P.coefficients.l P.extension f d).obj K ≅ G.obj K,
      G = (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).G ∧
      HEq adj (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).adjunction ∧
      (∀ K, HEq (γ K) (rationalIso P f c S d K)) ∧
      ∀ K, (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F.map
          (γ K).hom ≫ adj.counit.app K = localizedSmoothTrace P f c S d K) ∧
  (∃ GQ : generalAlgebraicallyClosedConstructibleCategory
        P.coefficients.l P.coefficients.Qbar Y ⥤
        generalAlgebraicallyClosedConstructibleCategory
          P.coefficients.l P.coefficients.Qbar X,
    ∃ adjQ : (operation P f c S .closed).F ⊣ GQ,
    ∃ γQ : ∀ K : generalAlgebraicallyClosedConstructibleCategory
        P.coefficients.l P.coefficients.Qbar Y,
        (commonSource P.coefficients.l P.coefficients.Qbar f d).obj K ≅ GQ.obj K,
      GQ = (operation P f c S .closed).G ∧
      HEq adjQ (operation P f c S .closed).adjunction ∧
      (∀ K, HEq (γQ K) (commonIso P f c S d K)) ∧
      ∀ (i : Index P.coefficients.l P.coefficients.Qbar)
        (K : sfRationalConstructibleCategory P.coefficients.l
          (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
            (AdicSmoothDualizing.fieldIndex (stageSetting P i))) Y),
        (operation P f c S .closed).F.map
            (γQ ⟨AdicSmoothDualizing.fieldIndex (stageSetting P i), K⟩).hom ≫
          adjQ.counit.app ⟨AdicSmoothDualizing.fieldIndex (stageSetting P i), K⟩ =
        descendedSmoothTrace P f c S d i K)

end Trace

section BaseChange
open ConstructibleExceptionalCoefficients
variable (P : PurityFiniteSetting.{u}) {X' X Y' Y : Scheme.{u}}
  [X'.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [Y'.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
  [QuasiCompact (X' ↘ Spec (.of P.field.k))]
  [IsSeparated (X' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
  [IsSeparated (Y' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X', Invertible (P.coefficients.l : X'.residueField x)]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y', Invertible (P.coefficients.l : Y'.residueField y)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
  [a.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
  [f.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
  [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (sq : IsPullback a f' f b) (c' : Compactification f') (c : Compactification f)
  (S' : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f'))
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension d f]

/-- Rational smooth exchange: inverse pulled-back purity, the canonical source
comparison, then base-changed purity. This is precisely the defining smooth exchange
of def-pur-smooth-pullback-exchange, transported to rational coefficients.
Source: thm-pur-smooth-base-change-coherence
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalSmoothExchange
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalDerivedPullback P.coefficients.l P.extension a).obj
        ((operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).G.obj K) ≅
      (operation P f' c' S' (.rational (AdicSmoothDualizing.fieldStage P))).G.obj
        ((rationalDerivedPullback P.coefficients.l P.extension b).obj K) :=
  (rationalDerivedPullback P.coefficients.l P.extension a).mapIso
      (rationalIso P f c S d K).symm ≪≫
    rationalSourceBaseChange P.coefficients.l P.extension a f' f b sq d K ≪≫
    rationalIso P f' c' S' d
      ((rationalDerivedPullback P.coefficients.l P.extension b).obj K)

/-- The same prescribed smooth exchange in the common-stage category.
Source: thm-pur-smooth-base-change-coherence and proof Step 6
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def commonSmoothExchange
    (K : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Y) :
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar a).obj
        ((operation P f c S .closed).G.obj K) ≅
      (operation P f' c' S' .closed).G.obj
        ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar b).obj K) :=
  (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar a).mapIso
      (commonIso P f c S d K).symm ≪≫
    commonSourceBaseChange P.coefficients.l P.coefficients.Qbar a f' f b sq d K ≪≫
    commonIso P f' c' S' d
      ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar b).obj K)

/-- The two paths around every Cartesian square commute, with no restriction on b.
Source: thm-pur-smooth-base-change-coherence, at both field coefficient stages
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def BaseChangeClause : Prop :=
  (∀ K : sfRationalConstructibleCategory P.coefficients.l P.extension Y,
    (rationalDerivedPullback P.coefficients.l P.extension a).map
        (rationalIso P f c S d K).hom ≫
        (rationalSmoothExchange P a f' f b sq c' c S' S d K).hom =
      (rationalSourceBaseChange P.coefficients.l P.extension a f' f b sq d K).hom ≫
        (rationalIso P f' c' S' d
          ((rationalDerivedPullback P.coefficients.l P.extension b).obj K)).hom) ∧
  ∀ K : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Y,
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar a).map
        (commonIso P f c S d K).hom ≫
        (commonSmoothExchange P a f' f b sq c' c S' S d K).hom =
      (commonSourceBaseChange P.coefficients.l P.coefficients.Qbar a f' f b sq d K).hom ≫
        (commonIso P f' c' S' d
          ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar b).obj K)).hom

end BaseChange

open ConstructibleExceptionalCoefficients

/-- All source settings for CompositionCoherence, including zero dimension and every object.
Source: proof Steps 1--7 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def CompositionCoherence (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [IsSeparated (Z ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  [∀ z : Z, Invertible (P.coefficients.l : Z.residueField z)]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
  (Sf : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (Sg : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := g))
  (Sfg : System P.coefficients.l P.coefficients.Qbar P.field
    P.coefficients.different (f := f ≫ g))
  (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
  [SmoothOfRelativeDimension (d + e) (f ≫ g)],
  RationalCompositionClause P f g cf cg cfg Sf Sg Sfg d e ∧
    CommonCompositionClause P f g cf cg cfg Sf Sg Sfg d e

/-- All source settings for TraceCoherence, including zero dimension and every object.
Source: proof Steps 1--7 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def TraceCoherence (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f],
  TraceClause P f c S d

/-- All source settings for BaseChangeCoherence, including zero dimension and every object.
Source: proof Steps 1--7 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def BaseChangeCoherence (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}}
  [X'.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [Y'.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
  [QuasiCompact (X' ↘ Spec (.of P.field.k))]
  [IsSeparated (X' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
  [IsSeparated (Y' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X', Invertible (P.coefficients.l : X'.residueField x)]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y', Invertible (P.coefficients.l : Y'.residueField y)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
  [a.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
  [f.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
  [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (sq : IsPullback a f' f b) (c' : Compactification f') (c : Compactification f)
  (S' : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f'))
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension d f],
  BaseChangeClause P a f' f b sq c' c S' S d

/-- Trace, geometric composition and arbitrary Cartesian base-change coherence for
one canonical purity family. This package does not reassert existence of purity.
Source: main-20261015, prop-pur-rational-purity-trace-coherence
(blueprint: prop-pur-rational-purity-trace-coherence). -/
structure RationalPurityTraceCoherence (P : PurityFiniteSetting.{u}) : Prop where
  trace : TraceCoherence P
  composition : CompositionCoherence P
  baseChange : BaseChangeCoherence P

/-- The canonical rational and Qbar purity isomorphisms preserve smooth trace,
geometric composition, and arbitrary Cartesian base change.
Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
prop-pur-rational-purity-trace-coherence, proof Steps 1--7
(blueprint: prop-pur-rational-purity-trace-coherence).
Proof: finite type over the field gives noetherian finite-dimensional schemes and
invertibility of l. Integral residue-Tor places each lattice in the uniform
finite-Tor domain. Apply the supplied integral reconstruction trace/coherence
diagrams, with the simultaneous scalar-compatible purity family. The canonical
unit orientation and its trace transpose identify this family with rationalIso.
Rational transport preserves functors, transformations, units, counits and their
equations. Hence the localized trace is F(gamma) followed by the same counit.
The exceptional geometric compositor is the adjunction mate of the proper/open
support compositor. Transport of the integral composition diagram therefore gives
RationalCompositionClause with this actual c_g,f. Smooth exchange is the specified
inverse-purity/source/purity composite; its inverse identity gives BaseChangeClause
for every Cartesian square, without any condition on the base-change map.
The scalar source, support and counit-mate comparisons preserve these paths and
their equality in every coefficient tower. Descend their common-stage representatives
using those same comparisons. This gives the common trace and composition equations,
and the common source/base-change square. Naturality at a split inclusion and
projection sandwiches both paths by the same endpoint maps, preserving all three
equations on direct summands, including zero and identity summands. -/
theorem rationalPurityTraceCoherence (P : PurityFiniteSetting.{u}) :
    RationalPurityTraceCoherence P := by
  sorry

end WeilConjectures.RationalPurityCoherence
