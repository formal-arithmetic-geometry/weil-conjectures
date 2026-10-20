# Retire the duplicate Koszul dual-complex module

## Reason

The assigned module is a retirement item in coord/retire-items.tsv (row keyed by
retire:Sheaf.RingTheory.KoszulRegularSequenceDualComplex). Its existing bodies contain
zero sorry holes. The adopted module
WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex already supplies every public
result, so retaining the duplicate can cause declaration collisions.

## Old

The current Sheaf module duplicates the adopted source module with the same suffix.

## New

Withdraw lean/Sheaf/RingTheory/KoszulRegularSequenceDualComplex.lean using deleted.txt.
Use the existing, unchanged source module with the same suffix.
A source comparison shows identical theorem signatures and proofs for unique comparison,
cohomology, augmentation, intrinsic roof formula, quotient multiplication, intrinsic Ext
comparison and localization. The only mathematical API difference is:

```lean
-- Sheaf version, after f g:
    (hregf : RingTheory.Sequence.IsKoszulRegular f)
    (hregg : RingTheory.Sequence.IsKoszulRegular g)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
-- Source version:
    (hregf : RingTheory.Sequence.IsKoszulRegular f)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
```

Both versions conclude exactly the same change-of-generators equality. The old proof
merely binds and ignores hregg. The source theorem applies under all the old hypotheses.
Its argument uses the basis for f, surjectivity of the conormal vector map and the two
normalization equations; it needs no regularity hypothesis on g. The source also publicly
imports Localization.Defs and privately imports SingleHomology, which do not change any
of these theorem meanings. No source file is edited.

## Users

Sheaf.TraceFormula.AlgebraicShriekCalculus is unclaimed in the current claim records.
Its only changed line replaces the private Sheaf import by the private source import.
Its signatures, definitions and proofs are byte-identical otherwise. No invocation of
the change-generators theorem occurs in it. Compilation verifies the migration.

The retire row lists four other former consumers. AffineKoszulScalarExtComparison,
KoszulExtOffRankStalk and KoszulRegularClosedImmersionPerfect no longer import the item
in the current library. FlatLCICanonicalAdjunction is quarantined: its preserved archive
imports the old module at line 39. Its rework row, archive and dependency node are retained.
When restoring that archive, replace that private import with the source import. The
archive has no invocation of change_generators, so no proof API adaptation is needed.
This delivery neither restores nor withdraws that independently quarantined module.

Retarget all three existing node lean records to the source module:
lem-sc-koszul-regular-sequence-dual-complex,
lem-sc-koszul-ext-determinant-roof and lem-sc-koszul-ext-determinant-multiplication.
The recorded primary statements are unchanged and exist verbatim in the source.
All declarations listed in the main node exist there, subject to the redundant-hypothesis
difference documented above. No node, dependency or unit step is removed. DAG parents
of the main node are lem-trf-flat-lci-canonical-adjunction,
lem-trf-relative-duality-polynomial-chart, lem-trf-algebraic-shriek-calculus,
lem-sc-koszul-regular-closed-immersion-perfect, lem-sc-koszul-ext-off-rank-stalk and
lem-sc-affine-koszul-scalar-ext-comparison. They still use precisely the same mathematical
result. The roof and multiplication nodes retain their existing parent links too.
The unit sk-thm-picard-duality and its realized steps are unchanged.

## Edge cases and validation

All replaced conclusions retain the original universe and ring assumptions, including
r = 0 and the zero quotient. No hypothesis is added to any consumer. Removing an unused
regularity hypothesis from the available replacement does not restrict those cases.
The import-direction tool permits the source import. The adapted consumer is compiled
through lcompile.py; deliver3.py repeats compilation and the required preflight/axiom
checks. The independent maintainer review and global build remain pending after delivery.

## Status

landed 20261020T233218-L-906547 2026-10-20 (merge of deliver/S2/Sheaf.RingTheory.KoszulRegularSequenceDualComplex)
