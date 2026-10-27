# WeilConjectures.PodCoefficientDescent.commonPullback / commonHom / commonTensor

## Reason

The new permitted-pair proof requires the existing common-stage object formulas.
Repeatedly elaborating those formulas through the raw unique-existence choices
makes this item exceed the compile limit. Record the formulas once in the proved
`Sheaf.Paper.PodCommonStageObjectNormalizations` interface and use its equality
proofs in the existing `copyObj` definitions. Their data remain definitionally
identical by proof irrelevance; only the equality proofs change. The new module
is publicly imported because these public definitions use it. No existing
signature, public import, global instance, or attribute is removed or changed.
The existing local irreducibility settings are moved earlier inside the item.
The returned packet also needed the local completed-coefficient and scalar
reduction barriers below. A first repair dry run otherwise took 69.6 seconds.
The profiled complete item with these barriers passes in 55.9 seconds.
The last signed-shift application is then reduced from 7.44 to 1.05 seconds
in an isolated check by letting apply infer its displayed parameters. The final
clean item compiles in 48.7 seconds and ContinuationB against it in 41.0 seconds.
A new dry run of the reviewed item took 65.3 seconds. The current repair keeps
the existing category wrappers abstract locally, following the semilinear
composition proof. Preadditive.fullSubcategory,
StageSystem.PairCategory.categoryStruct and Linear.homModule are cached after
the generic helpers. ObjectProperty.FullSubcategory.category is cached only
after end Reindex: the earlier integral signatures project underlying morphisms
and need its original transparency. The resulting clean item compiles in
39.3 seconds. There is no instance registration in this module, and these
attributes are local. No target statement or mathematical meaning changes.

## Old

```lean
def commonPullback := (commonStageDerivedPullback l Ω g).copyObj
  (commonStagePullbackObject l Ω g)
  (fun P ↦ eqToIso ((commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1 P))

def commonHom (W : Scheme.{u}) := (commonStageDerivedInternalHom l Ω W).copyObj
  (commonStageHomObject l Ω W)
  (fun P ↦ eqToIso ((commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose_spec.1 P))

def commonTensor (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
  (commonStageDerivedTensor l Ω W).copyObj
    (fun P ↦ commonStageTensorObject l Ω W P.1 P.2)
    (fun P ↦ eqToIso ((commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1 P.1 P.2))
```

## New

```lean
def commonPullback := (commonStageDerivedPullback l Ω g).copyObj
  (commonStagePullbackObject l Ω g)
  (fun P ↦ eqToIso ((podCommonStageObjectNormalizations l Ω).1 g P))

def commonHom (W : Scheme.{u}) := (commonStageDerivedInternalHom l Ω W).copyObj
  (commonStageHomObject l Ω W)
  (fun P ↦ eqToIso ((podCommonStageObjectNormalizations l Ω).2.2 W P))

def commonTensor (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
  (commonStageDerivedTensor l Ω W).copyObj
    (fun P ↦ commonStageTensorObject l Ω W P.1 P.2)
    (fun P ↦ eqToIso ((podCommonStageObjectNormalizations l Ω).2.1 W P.1 P.2))
```

The local header barrier becomes:

```lean
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
```

After the generic helpers, add these local category caches:

```lean
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

attribute [local irreducible] Linear.homModule
```

After end Reindex and before CommonStage, also add:

```lean
attribute [local irreducible] ObjectProperty.FullSubcategory.category
```

Before common_signedShift_images, retain the rational operation wrappers:

```lean
attribute [local irreducible] shiftedPullbackInput rationalDerivedPullback
  rationalDerivedInternalHom
```

Its complete proof is now:

```lean
  apply (inclusion L : Stage l Ω X L ⥤
    generalAlgebraicallyClosedConstructibleCategory l Ω X).congr_map
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      apply rational_signed_shifts
  all_goals assumption
```

## Users

`tools/downstream.py --uses` for each of the three names finds only the item
itself. F8 split the old sole direct importer into Base, ContinuationA, ContinuationB
and its main re-export. Base, ContinuationA and the main re-export are tested
without modification. ContinuationB needs only the local elaboration-context
repair described in g8-pod-continuation-sequential-elaboration.md.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | G8 | Replace equality proof terms; preserve data and signatures. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed (F8 split) | Current re-export retained verbatim and checked. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluationBase | unclaimed (F8 split) | Current source retained verbatim and checked. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA | unclaimed (F8 split) | Current source retained verbatim and checked. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB | unclaimed (F8 split) | All declarations and proofs retained; local elaboration context repaired and checked. |

## Status

landed 20261027T233952-L-4145821 2026-10-27 (merge of deliver/G8/Sheaf.Paper.PodReindexingHomCoefficientDescent)
