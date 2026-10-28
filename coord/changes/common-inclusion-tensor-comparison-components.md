# WeilConjectures.commonInclusionTensorComparison

## Reason

The unclaimed Sheaf definition assembled a natural model isomorphism, whiskered its coefficient units, composed the natural isomorphisms, and inverted. Projecting its hom component in the assigned tensor/pullback proof made the kernel repeatedly unfold concrete scalar-localized composition dictionaries; isolated component formulas exceeded 120 seconds. Construct the same inverse corrected-model isomorphisms directly with `NatIso.ofComponents`. A new proved generic naturality theorem supplies the proof field. The signature, universes, binders, attributes, objects, and component maps are preserved.

The new proved theorem is publicly imported because an exposed public definition uses it for its naturality field; Lean refuses a private import here. The existing model-naturality theorem is untouched. No source-library module or target statement changes.

## Old

```lean
@[irreducible] def commonInclusionTensorComparison
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)] (E : Index l Ω) :
    rationalDerivedTensor l (Coefficient.{u} l Ω E) W ⋙
        inclusion (l := l) (Ω := Ω) (Y := W) E ≅
      (inclusion (l := l) (Ω := Ω) (Y := W) E).prod
          (inclusion (l := l) (Ω := Ω) (Y := W) E) ⋙
        commonStageDerivedTensor l Ω W := by
  let I := inclusion (l := l) (Ω := Ω) (Y := W) E
  let R := rationalDerivedTensor l (Coefficient.{u} l Ω E) W
  let U := (operationStageTransitionIso l Ω W E E le_rfl) ≪≫ unitor l Ω W E
  let a : (I.prod I) ⋙ commonStageDerivedTensor l Ω W ≅
      (((stageSystem l Ω W).T (le_rfl : E ≤ E)).prod
        ((stageSystem l Ω W).T (le_rfl : E ≤ E))) ⋙ (R ⋙ I) :=
    NatIso.ofComponents (fun K ↦ commonInclusionTensorModel l Ω W E K.1 K.2)
      (fun f ↦ commonInclusionTensorModel_naturality l Ω W E f.1 f.2)
  exact (a ≪≫ Functor.isoWhiskerRight (NatIso.prod U U) (R ⋙ I)).symm
```

## New

```lean
@[irreducible] def commonInclusionTensorComparison
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)] (E : Index l Ω) :
    rationalDerivedTensor l (Coefficient.{u} l Ω E) W ⋙
        inclusion (l := l) (Ω := Ω) (Y := W) E ≅
      (inclusion (l := l) (Ω := Ω) (Y := W) E).prod
          (inclusion (l := l) (Ω := Ω) (Y := W) E) ⋙
        commonStageDerivedTensor l Ω W := by
  let I := inclusion (l := l) (Ω := Ω) (Y := W) E
  let R := rationalDerivedTensor l (Coefficient.{u} l Ω E) W
  let U := (operationStageTransitionIso l Ω W E E le_rfl) ≪≫ unitor l Ω W E
  exact NatIso.ofComponents
    (fun K ↦ (commonInclusionTensorModel l Ω W E K.1 K.2 ≪≫
      I.mapIso (R.mapIso (Iso.prod (U.app K.1) (U.app K.2)))).symm)
    (fun f ↦ tensoratorFromModel_naturality I R (commonStageDerivedTensor l Ω W) U
      (fun K ↦ commonInclusionTensorModel l Ω W E K.1 K.2)
      (fun f ↦ commonInclusionTensorModel_naturality l Ω W E f.1 f.2) f)
```

## Users

| module | ownership / delivery role | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonStageInclusionTensorNaturality | unclaimed | Component construction refactored; existing theorem, signatures and attributes preserved. |
| Sheaf.Paper.CommonProjectionTensorComparison | unclaimed | Direct importer and named user; compiled unchanged against the repair. |
| Sheaf.Paper.AdicCompletedTensorStageComponent | unclaimed | Direct importer and named user; compiled unchanged against the repair. |
| Sheaf.Paper.AdicCompletedTensorStageNaturality | unclaimed | Indirect importer naming the definition; compiled unchanged against the repair. |
| Sheaf.Paper.CommonProjectionPullbackTensorCompatibility | P1 | Assigned proof uses the unchanged comparison. |
| Sheaf.Paper.CommonProjectionPullbackTensorModels | P1 | New proved finite-model square uses the efficient component formula. |
| Sheaf.Paper.CommonProjectionPullbackTensorComponent | P1 | Existing component theorem moved; uses the repaired comparison and unchanged operation definitions. |
| Sheaf.Paper.CommonProjectionPullbackTensorOperations | P1 | Four existing definitions relocated verbatim, plus the generic component-square predicate; publicly re-exported by the item. |
| Sheaf.Paper.CommonProjectionTensorComparisonNormalization | P1 | New proved normalization lemma; uses the repaired comparison. |
| Sheaf.Paper.CommonProjectionProperFactor | not modified | Direct importer of the item; compiled unchanged against the split. |
| Sheaf.Paper.HigherTensorIdentityComposition | not modified | Direct importer of the item; compiled unchanged against the split. |
| Sheaf.Paper.CommonProjectionProperTensorCompatibility | not modified | Direct importer of the item; compiled unchanged against the split. |
| Sheaf.Paper.ProjectionIdentityTensorUnit | not modified | Direct importer of the item; compiled unchanged against the split. |
| Sheaf.Paper.CommonProjectionOpenPullbackTensor | not modified | Mentions the inclusion tensorator only in a proof comment; no Lean use. |
| Sheaf.Paper.ProjectionIdentityProperCounit | not modified | Uses the unchanged pullback and transport definitions; compiled unchanged against the split in 47.8 seconds. |

`tools/downstream.py --uses commonInclusionTensorComparison` lists the first four existing modules as named users (including the defining module). Its other 316 downstream modules inherit the same natural isomorphism and require no source adaptation. The delivery tool also checks related importers. The three unchanged consumer copies used for compilation are removed before delivery.

## Item module split

The assigned module spent 43 seconds serializing its `.olean` file, in addition to 40 seconds elaborating and checking it. After improving the slow concrete tensorator above, separate its existing declarations into three modules: the four unchanged operation definitions in `CommonProjectionPullbackTensorOperations`, the proved existing component theorem in `CommonProjectionPullbackTensorComponent`, and the existing universal bridge and final theorem in the original item module. The original module publicly imports the component, which publicly imports the operations, so existing importers retain every original declaration. The four definition bodies and signatures stay identical. Every existing declaration keeps its name, binders, universes and attributes. The component conclusion is factored through the explicit generic predicate described below. Only proved private helpers are moved alongside the component. The component's DAG attachment follows it; the operations node records the existing definitions. No original declaration is removed from the library.

The isolated original expanded component signature itself took 44 seconds to serialize. Factor its equation through the generic `projectionTensorComparisonComponent`, whose body is the literal five-factor equation, with the same functors, transformations and comparison isomorphisms as arguments. The component theorem retains every hypothesis and proves this predicate by the existing complete normalization argument. Unfolding the predicate recovers its previous conclusion definitionally (`Iso.symm.inv` is the original comparison hom). No assumption is added and no conclusion is weakened. This changes the written conclusion of an auxiliary theorem, not any declaration of `Challenge.lean`. The component node's Lean signature records the predicate form.

The four direct importers of the assigned module (`CommonProjectionProperFactor`, `HigherTensorIdentityComposition`, `CommonProjectionProperTensorCompatibility`, and `ProjectionIdentityTensorUnit`) compile unchanged against the split. Their temporary source copies are removed from the delivery. All twelve delivery modules compile without profiling options; the split component and facade take 40.1 and 30.5 seconds respectively.

## Status

landed 20261028T081750-L-2780519 2026-10-28 (merge of deliver/P1/Sheaf.Paper.CommonProjectionPullbackTensorCompatibility)
