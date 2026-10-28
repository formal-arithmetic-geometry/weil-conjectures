# WeilConjectures.PodReindexingCoherence.comparison_core_tensor_model_exists

## Reason

The old theorem asserts an exact representative equation for two independently
arbitrary isomorphisms. This is false. Negating only `tensor` negates the left
side, while fixing the right side. Specialize to identity reindexing on a
nonempty point, l = 3, E = Q_3, s = some 0, and the constant coefficient unit
complex in degree zero. Its tensor square has nonzero F_3 cohomology in degree
zero. Every displayed comparison is an isomorphism. Applying the two alleged
equations would imply an invertible morphism equals its negative, and hence
1 = -1 on F_3, a contradiction.

The blueprint, dual-Tate compatibility Steps 1 and 2, specifies the canonical
tensor comparison. The corrected theorem constructs its derived comparison by
descent from the pure-normalized tensor-chain data. The arbitrary `t.tensor`
field supplied by the preliminary tensor-data existence result is unused; the
new comparison comes with the exact required representative normalization.

Naturality of the chain comparison is proved by cancellation and pure-generator
extensionality. K-flat preservation is already proved in
`podReindexing_resolution_preservation`. The proved K-flat localization and
Mathlib full faithfulness descend the explicit composite of the two tensor
models and localization factorization. The preimage equation proves the
normalization by cancellation. No new unproved intermediate is introduced.

## Old

```lean
theorem comparison_core_tensor_model_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (tensorChain : ∀ P L : K l E Y s,
      (podReindexingComplexFunctor l E g s).obj ((total l E Y s).obj (P, L)) ≅
        (total l E X s).obj ((podReindexingComplexFunctor l E g s).obj P,
          (podReindexingComplexFunctor l E g s).obj L))
    (tensor : SY.tensor ⋙ podReindexingDerivedFunctor l E g s ≅
      ((podReindexingDerivedFunctor l E g s).prod (podReindexingDerivedFunctor l E g s)) ⋙
        SX.tensor) :
    Nonempty (ComparisonCoreTensorModelData l E g s SX SY TX TY tensorChain tensor)
```

## New

```lean
theorem comparison_core_tensor_model_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (t : ComparisonCoreTensorData l E g s SX SY TX TY) :
    ∃ tensor : SY.tensor ⋙ podReindexingDerivedFunctor l E g s ≅
        ((podReindexingDerivedFunctor l E g s).prod (podReindexingDerivedFunctor l E g s)) ⋙
          SX.tensor,
      Nonempty (ComparisonCoreTensorModelData l E g s SX SY TX TY t.tensorChain tensor)
```

## Users

`tools/downstream.py --direct --uses comparison_core_tensor_model_exists`
finds the following direct importer and the item itself as the only modules
mentioning the changed name. The full transitive scan likewise finds only
these two mentions. All other indirect consumers see the unchanged signature
and unchanged `Comparison` fields of `comparison_core_exists`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PodReindexingComparisonCoreTensorModel | T8 | Correct and prove the normalized-choice theorem; `ComparisonCoreTensorModelData` is unchanged. |
| Sheaf.Paper.PodReindexingComparisonCore | unclaimed in shared claim records | Replace the old two-argument application with the new tensor-data application and use its returned tensor. Its theorem signature, all other fields and imports stay identical. |

The two new proof modules, `PodReindexingTensorChainNaturality` and
`PodReindexingTensorPresentationComparison`, are fully proved. The latter also
constructs the K-flat full-subcategory lift explicitly from the existing
preservation theorem. Their API separates pure-generator naturality, the
comparison on representatives and the localization descent.

The parent proof node is updated to name the actual three component results.
The item node fixes the trailing period in its `lean.module` attachment, records
the corrected statement and the new proof dependencies, and records a complete
statement-change audit. No existing node explicitly cited this item in
`stmt_deps` or `proof_deps`; the actual Lean caller was missing that DAG edge,
which this delivery adds. The unit has no realized steps to bypass.

The proof-only forced parent adaptation is the three-line change obtaining
`tensor` together with `m`, then assigning `tensor := tensor`. Compilation of
both files against the delivery validates the complete affected direct chain.
No target signature or definition used by a target is changed.

## Status

landed 20261028T072452-L-1952327 2026-10-28 (merge of deliver/T8/Sheaf.Paper.PodReindexingComparisonCoreTensorModel)
