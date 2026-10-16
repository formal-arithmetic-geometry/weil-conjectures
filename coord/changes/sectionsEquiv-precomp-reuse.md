# AlgebraicGeometry.Etale.sectionsEquiv_precomp

## Reason

The returned delivery was refused for proving the same sections-precomposition identity
already present in `AbelianRepresentableGeneratorCoherence` and
`EtaleResolutionSectionCanonicalOpenToOpenCycle`. Both existing lemmas are private.
Expose the existing proved lemma in the unclaimed generator-coherence module, import that
module in the item, and remove the item's duplicate. This reuses the existing proof;
no mathematical statement or definition changes.

## Old

```lean
private lemma sectionsEquiv_precomp {X : Scheme.{u}} {A B : X.Etale}
    (a : A ⟶ B) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (etaleOpenFreeSheaf X).obj B ⟶ F) :
    EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology A F
      ((etaleOpenFreeSheaf X).map a ≫ f) =
      F.obj.map a.op (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology B F f)
```

## New

```lean
lemma sectionsEquiv_precomp {X : Scheme.{u}} {A B : X.Etale}
    (a : A ⟶ B) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (etaleOpenFreeSheaf X).obj B ⟶ F) :
    EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology A F
      ((etaleOpenFreeSheaf X).map a ≫ f) =
      F.obj.map a.op (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology B F f)
```

The existing proof is unchanged. Only `private` is removed. The existing generator node's
`lean.declarations` records the newly available helper already used in its proof step 3.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence | unclaimed | Existing proof and calls unchanged; the proved helper becomes public. |
| Sheaf.AlgebraicGeometry.EtaleOpenCohomologyRestrictionCompatibility | G3 | Import generator coherence and use `Etale.sectionsEquiv_precomp`; remove the duplicate private lemma. |

`tools/downstream.py` found 719 transitive importers of generator coherence and no use of
`sectionsEquiv_precomp` among them. No downstream adaptation is needed. The separate private
lemma in `EtaleResolutionSectionCanonicalOpenToOpenCycle` keeps its private Lean name and
continues to coexist with the public theorem; its module is not changed by this delivery.
No target type, definition, public import, or existing public signature changes.

## Status

landed 20261016T054836-L-157543 2026-10-16 (merge of deliver/G3/Sheaf.AlgebraicGeometry.EtaleOpenCohomologyRestrictionCompatibility)
