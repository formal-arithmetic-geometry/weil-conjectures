# WeilConjectures.AdicQbarRealization.completedScalarReindex

## Reason

Construct explicit shared scalar maps so the two independent pieces of the assigned
scalar compatibility proof refer to identical normalized maps. No old interface is
changed. This record documents additions rather than a repair of an existing datum.

## Old

The new modules and declarations did not exist. The existing theorem statement of
`realizationIntegralReindex_scalar` and its existing public imports stay verbatim.

## New

`AdicReindexScalarData` defines `completedReindexModel`, `scalarExactModel`,
`completedScalarReindex`, and `nativeScalarTransition`, and proves
`completedRingReindex_eq`. All data bodies are concrete composites or selection from
an existing unique normalized existence theorem. `AdicReindexScalarSource` proves
`realizationStageObject_eq`, defines `realizationScalarArrow` and
`realizationReindexSource`, and states `realizationReindexSource_scalar`. It also
constructs the generic `realizationReindexSourceComposite` and proves its component
and factorization formulas before specialization to derived coefficient categories.
`AdicReindexBalancedScalar` states `integralReindex_balanced_scalar`.
The principal new comparison has this verbatim declaration (l, E, L and ι are
section variables with the finite-extension instances recorded in the module):

```lean
def completedScalarReindex {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podCompletedDerivedInverseImage l E g ⋙ completedDerivedScalarExtension l E L ι X ≅
      completedDerivedScalarExtension l E L ι Y ⋙ podCompletedDerivedInverseImage l L g :=
  Functor.isoWhiskerLeft _ (scalarExactModel l E L ι X).symm ≪≫
    Functor.isoWhiskerRight (completedReindexModel l E g) _ ≪≫
    isomorphismScalarTensorDerived l E L ι g ≪≫
    Functor.isoWhiskerLeft _ (completedReindexModel l L g).symm ≪≫
    Functor.isoWhiskerRight (scalarExactModel l E L ι Y) _

```

The other exact signatures are recorded in their new DAG attachments and Lean files.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicRealizationReindexScalar | G8 | Uses the two scalar squares only in its proof. |
| Sheaf.Paper.AdicReindexScalarSource | G8 (new) | Uses the concrete scalar reindexing map in its statement. |
| Sheaf.Paper.AdicReindexBalancedScalar | G8 (new) | Uses the same map in its ambient statement. |

No existing foreign consumer is adapted; no existing definition, instance, attribute,
public import, or signature changes. Indirect consumers see the same original theorem.

## Status

landed 20261028T055656-L-794613 2026-10-28 (merge of deliver/G8/Sheaf.Paper.AdicRealizationReindexScalar)
