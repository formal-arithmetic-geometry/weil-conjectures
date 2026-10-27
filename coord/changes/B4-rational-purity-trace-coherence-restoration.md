# RationalPurityTraceCoherence elaboration and restoration

## Reason

Restore the quarantined source listed in coord/rework.tsv and repair its elaboration
against the current coefficient-category interfaces. The assigned failure was the
deterministic heartbeat timeout at the rational support component `.hom.app K`
(archived line 527); that component now uses an explicit category transport and
elaboration boundary. Preserve every declaration and
all five public imports. Remove the source's permissive backward transparency
options and explicitly enable both checks to override the package's false default.
File-local irreducibility settings protect existing derived, tensor,
scalar-Hom and canonical-purity constructions; local priorities select existing
category structures. These settings do not export attributes or change data.

The three trace definitions receive explicit result types. The rational trace's
composite is unchanged. The model trace is written as F.map of the same purity
morphism followed by the same adjunction counit: Adjunction.homEquiv_symm_apply
proves equality with the old inverse Hom-equivalence, with no new hypothesis.
At a common stage, commonCategory_eq transports this same Hom to the stage category
before inclusion. That theorem is proved by unfolding the two category instances
and rfl. The support-compositor formula uses this same equality to type the same
rational component, and specifies the inclusion's target scheme explicitly.
No functor, adjunction, field model, root normalization or comparison is replaced.
The trace formulas were checked in isolation before the complete-file performance check.

Six existing auxiliary theorem holes have complete proofs from existing
declarations and elementary algebra. In particular, inverse tensor concatenation
uses the already normalized multiplication theorem and a genuine uniqueness proof
from scalar linearity and tensor balancing. No definition contains a new proof
hole and no consumer module is edited. Details and the two remaining holes are
listed in report.md.

## Old

The archived source has these permissive commands:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

### localizedSmoothTrace

```lean
def localizedSmoothTrace
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :=
  (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F.map
      (rationalSourceComparison P f d K).hom ≫
    (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).q.inv.app
      (integralSource P f d (representative P K)) ≫
    (rationalization P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) Y).map
        (integralTraceTranspose P f c S d (representative P K)) ≫
    (eqToIso (representative_eq P K)).hom
```

### modelSmoothTrace

```lean
def modelSmoothTrace
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) Y) :=
  ((S.ring.operation c (.rational
      (commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).adjunction.homEquiv _ _).symm
    (smallModelIso P f c S d K).hom
```

### descendedSmoothTrace

```lean
def descendedSmoothTrace (i : Index P.coefficients.l P.coefficients.Qbar)
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex (stageSetting P i))) Y) :=
  (operation P f c S .closed).F.map
      (commonSourceComparison P.coefficients.l P.coefficients.Qbar f d
        ⟨AdicSmoothDualizing.fieldIndex (stageSetting P i), K⟩).hom ≫
    (S.common.commonComparison c (AdicSmoothDualizing.fieldIndex (stageSetting P i))).q.inv.app
      ((rationalSource P.coefficients.l
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex (stageSetting P i))) f d).obj K) ≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion
        (AdicSmoothDualizing.fieldIndex (stageSetting P i))).map
      (modelSmoothTrace (stageSetting P i) f c S d K)
```

### commonSupportComposition_existsUnique

```lean
theorem commonSupportComposition_existsUnique :
    ∃! c : (Sf.ring.operation cf .closed).F ⋙ (Sg.ring.operation cg .closed).F ≅
        (Sfg.ring.operation cfg .closed).F,
      ∀ (i : Index P.coefficients.l P.coefficients.Qbar)
        (K : Stage P.coefficients.l P.coefficients.Qbar X i),
        (c.hom.app ⟨i,K⟩) =
          (Sg.ring.operation cg .closed).F.map ((Sf.common.commonComparison cf i).q.inv.app K) ≫
          (Sg.common.commonComparison cg i).q.inv.app
            ((Sf.ring.operation cf (.rational
              (commonField P.coefficients.l P.coefficients.Qbar i))).F.obj K) ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion i).map
            ((rationalSupportComposition P f g cf cg cfg Sf Sg Sfg
              (commonField P.coefficients.l P.coefficients.Qbar i)).hom.app K) ≫
          (Sfg.common.commonComparison cfg i).q.hom.app K := by
  sorry
```

## New

Both checks are explicitly enabled, overriding the package defaults:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

File-local protection commands are:

```lean
attribute [-instance] integralOperationsSiteSmall scalarReductionSiteSmall
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
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom

namespace WeilConjectures.RationalPurityCoherence
open FrobeniusCoefficientTwists RationalSmoothPurityCanonical

attribute [local irreducible] integralSource integralTraceTranspose rationalSourceComparison
  smallModelIso rationalIso commonIso
```

The remaining local protection is staged after the construction whose defining
object equation must remain visible:

```lean
-- after lineAdd_existsUnique, whose proof evaluates the module isomorphisms
attribute [local irreducible] Functor.mapIso ordinaryModel
-- after rationalLinePull
attribute [local irreducible] rationalDerivedPullback
-- after lineSingleTensor
attribute [local irreducible] coefficientTotalTensor
-- after rationalShiftedLineAdd
attribute [local irreducible] rationalDerivedTensor
-- after the Lines section
attribute [local irreducible] rationalSource commonSource commonSourceComparison
  commonStageDerivedTensor completedIntegralCommRingSheafUnrestricted
-- after commonPullInclusion, and again after the CommonSources section
attribute [local irreducible] commonStageDerivedPullback
```

The Trace section gives the existing published coefficient-model instances higher
priority, so all trace formulas use the same named presentations:

```lean
attribute [local instance 3000] commonModelField commonModelAlgebra commonModelFinite
```

These are the published field, algebra and finite-dimensionality structures from
commonField; no new field model or algebra structure is chosen. The type-checker
can compare their named presentations directly. The exclusions of generic site
instances above match the exclusions in PuritySourceTransports; ordinary scheme
instances still supply those structures. Completion and tower guards follow the
settings used in CanonicalTateComparisons.
The file also sets `Elab.async` to false, as CanonicalTateComparisons does, to avoid
concurrent normalization of these large constructions. With the staged guards,
explicit trace interfaces and synchronous elaboration, the complete restored source
is checked through lcompile.py and the delivery compiler. No compiler limit is raised. All
profiling settings and diagnostic commands are removed.

The common-source, geometric-composition and trace sections locally prefer
IntermediateField.algebra' and ConstructibleExceptionalCoefficients.category at
priority 2000. The latter two sections also locally protect ScalarLocalization.category.
All new scalar-linearity helpers are private proved theorems, used only in a proof.
Their section uses the tensor product's completed commutative-ring presentation.
A private abbreviation projects the native section-module structure
`(M.val.obj U).isModule` and is registered as a local instance only within
`RootTensorProof`. A second private abbreviation `sectionSmul` applies this exact
action with its scalar ring specified explicitly; it accepts the original
completed coefficient sections. The existing coefficient commutative-ring
instance is selected there as well. These are exactly the existing ring and
action data. The induction step uses the canonical sheafification unit's linearity
and the tensor scalar identity directly, fixing the existing module/site universes; tensor balancing is mapped through the
sheafification unit and the canonical tensor comparison. These avoid rewriting
across the two definitionally equal ring presentations. No imported definition's
reducibility is weakened and no unsafe option is used.

The good-single proof uses the rank-one clause of `pur_twist_sheaf_locally_free`
explicitly, then `coefficientTwistLine_exact` and the proved private helpers
`single_kFlat` and `single_flat_terms` from `FlatSingleDerivedNormalization`.
Its `import all` is private and is used only by this theorem proof.

### localizedSmoothTrace

```lean
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
```

### modelSmoothTrace

```lean
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
```

### descendedSmoothTrace

```lean
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
```

### commonSupportComposition_existsUnique

```lean
theorem commonSupportComposition_existsUnique :
    ∃! c : (Sf.ring.operation cf .closed).F ⋙ (Sg.ring.operation cg .closed).F ≅
        (Sfg.ring.operation cfg .closed).F,
      ∀ (i : Index P.coefficients.l P.coefficients.Qbar)
        (K : Stage P.coefficients.l P.coefficients.Qbar X i),
        (c.hom.app ⟨i,K⟩) =
          (Sg.ring.operation cg .closed).F.map ((Sf.common.commonComparison cf i).q.inv.app K) ≫
          (Sg.common.commonComparison cg i).q.inv.app
            ((Sf.ring.operation cf (.rational
              (commonField P.coefficients.l P.coefficients.Qbar i))).F.obj K) ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Z) i).map
            (by
              have e := rationalSupportComposition P f g cf cg cfg Sf Sg Sfg
                (commonField P.coefficients.l P.coefficients.Qbar i)
              have t := e.hom.app K
              exact (commonCategory_eq P Z i) ▸ t) ≫
          (Sfg.common.commonComparison cfg i).q.hom.app K := by
  sorry
```

## Users

The read-only tools/downstream.py query with --allow-missing reports zero live
importers, as expected for a quarantined module. A source search over lean/ and
quarantine/ finds no external Lean importer or reference to its declarations.
The DAG attachment and outstanding parent dependencies are retained. Absence of
live importers is not used to withdraw the item. No consumer needs adaptation:
the normalized mathematical interfaces and maps are the same. The independent
reader should check the adjunction formula and category transports above as part
of the usual review of these definition-sensitive statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | B4 | Restored archive, local elaboration commands, explicit result types, equivalent trace formulas and auxiliary proofs. |

No source-library declaration, target statement, target hypothesis or target
conclusion is changed. All original construction data are retained up to the
explicitly cited, proved categorical equalities.

## Status

landed 20261026T065231-L-2761348 2026-10-26 (merge of deliver/B4/Sheaf.SecSmoothPurity.RationalPurityTraceCoherence)
