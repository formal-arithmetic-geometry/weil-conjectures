# AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv_naturality

## Reason

Complete the explicitly listed retirement of the proved Sheaf duplicate of
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`.
Repair the unmerged F2 delivery at `dfe7664f3` on the current `sheaf-dag` base.
The consumer migration reviewed in B2's landing
`20261020T230711-L-602865` is already present and is preserved verbatim.

This complete record is delivered at
`coord/changes/retire-module-cohomology-ext-resolution-naturality-F2.md`.
No external reviewer fix is needed. If a reviewer changes this record, the
stage-3 `--apply-fixes` basename is
`retire-module-cohomology-ext-resolution-naturality-F2.change.md`, as specified
by `tools/batch_land.py`; using the ordinary `.md` basename caused the return.

## Old

The duplicate module supplies the resolution-normalized comparison and this
already proved theorem (signature verbatim):

```lean
theorem moduleCohomologyExtResolutionEquiv_naturality (X : Scheme.{u}) (q : ℕ)
    (F G : X.Modules) (φ : F ⟶ G)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleCohomologyExtResolutionEquiv X G q
      (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
      H.map φ q (moduleCohomologyExtResolutionEquiv X F q x)
```

Its public caches are `comparisonHasSheafify` and `comparisonHasExt`; its
composition helper is `ExtEdgeResolution.sectionsComparisonNatIso`. These
helpers already exist in the adopted upstream extension module.

## New

Withdraw only
`lean/Sheaf/AlgebraicGeometry/ModuleCohomologyExtResolutionNaturality.lean`
through `deleted.txt`. The DAG node remains attached to the upstream theorem
with the identical displayed naturality signature. Its mathematical statement,
proof steps, three dependencies, parent references and unit route are retained.
Only its Lean note and proof-origin description record the final retirement.
The adopted upstream module and extension are not edited.

Every consumer already imports the adopted source owner, its extension or a
consumer that publicly imports them. Their current definitions, signatures and
proofs are retained. No adaptation is necessary in this packet. No target
signature, hypothesis, or mathematical conclusion changes.

## Users

No current live module imports the retired Sheaf module. The following former
consumers from the returned packet were already migrated by the reviewed B2
delivery. The remaining inventory consumers have adopted upstream owners.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison | unclaimed | No edit; publicly imports the adopted source owner and extension. |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphismExists | unclaimed | No edit; imports the adopted extension. |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback | unclaimed | No edit; imports the adopted extension. |
| Sheaf.AlgebraicGeometry.CoherentEtaleEffacingSequence | unclaimed | No edit; imports the adopted extension. |
| Sheaf.AlgebraicGeometry.CoherentPowerComparison | unclaimed | No edit; imports the adopted extension. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback | A2 | No edit; the canonical public import supplies the adopted comparison. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | unclaimed | No edit; keeps its current complete proof and canonical public import. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | F4 | No edit; keeps the reviewed public FMap and canonical imports. |

The inventory also names
`AbelianExtSectionsCocycleNormalization`, `ModuleCohomologyExtResolutionEdge`,
`ModuleCohomologyExtResolutionNormalization`, `ModuleCohomologyExtSectionsFactorization`,
`ModuleCohomologyExtStandardResolutionFormula`, `ModuleCohomologyStandardSectionsFactorization`,
and `TerminalSourceSectionsEvaluation`. Their adopted source modules continue
to use the adopted source owner or extension. No upstream declaration is
removed, altered, or given an incomplete proof.

The three historical quarantine archives for `CoherentFrobeniusPullback`,
`QcoherentNormalizedComparison`, and `QcoherentNormalizedPullbackSquare` retain
their former imports. Their restored live versions already use the migrated
comparison API. No quarantine archive or mathematical parent is withdrawn.

Server validation through `lcompile.py --all` compiled the empty withdrawal
module and a joint import of the eight live consumers with the adopted owner
and extension. The adopted naturality theorem's axiom list contains only
`propext`, `Classical.choice`, and `Quot.sound`.

## Status

landed 20261021T001118-L-1372142 2026-10-21 (merge of deliver/F2/Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality)
