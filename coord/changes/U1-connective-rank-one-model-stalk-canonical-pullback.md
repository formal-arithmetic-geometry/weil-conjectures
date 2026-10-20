# AlgebraicGeometry.surjective_stalk_homology_of_connective_rank_one_model

## Reason

Restore the complete module from the quarantine path named in `coord/rework.tsv`.
Its archived public derived-pullback import is now an empty withdrawn module.
The theorem signature needs the canonical adopted `derivedPullback` declaration,
so replace that import by its adopted source module. Preserve all declaration
signatures, docstrings, visibility, the private helper used by the quarantined
fibre-criterion consumer, and the mathematical proof route.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

The theorem statement and its hypotheses and conclusion are unchanged. The proof
now explicitly supplies `IsIso (H.map c.inv)`, its epimorphism instance, and
`IsIso (H.map e.hom)` rather than asking typeclass search to reconstruct them.
The degree-zero component epimorphism is obtained directly by `IsSplitEpi.epi`.
No definition, target statement, or mathematical interface changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk | U1 | Restore complete proof with the canonical import. |
| Sheaf.AlgebraicGeometry.PerfectLocalDegreeZeroUnit | quarantined; separate rework | Existing application has the identical arguments and conclusion. |
| Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion | quarantined; separate rework | Both uses of the existing private strictly-perfect helper remain valid. |

`tools/downstream.py` reports the item as unknown because it is quarantined.
Searching both live Lean roots and `quarantine/Sheaf/` finds exactly the two
external consumers listed above. The first passes the same affine neighbourhood,
model, vanishing and rank-one witnesses, derived isomorphism and residue hypothesis.
The second imports `all` and uses the unchanged private helper twice. Neither
consumer needs a signature or proof adaptation. They remain separate restoration
items; no quarantined file or dependency is withdrawn. The explicit helper and
public theorem consumer checks are compiled with this restoration.

## Status

landed 20261020T235629-L-1198386 2026-10-20 (merge of deliver/U1/Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk)
