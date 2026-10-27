# ProEtaleSectionModuleFunctors proof elaboration

## Reason

Close the normalized section-direct-image theorem and reuse existing proved
internal pairing and tensor-comparison APIs. Avoid repeated expansion of the
large coefficient constructions. No public signature or operation changes.

## Old

The private canonical pairing used:

```lean
  letI : (CondensedRing.upperStar Λ f).OplaxMonoidal :=
    (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal
  exact (CondensedRing.upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
```

The two strong instances used the direct expression
`Functor.Monoidal.ofOplaxMonoidal` on their respective pullbacks.

## New

The private canonical pairing uses the existing named strong instance:

```lean
  letI : (CondensedRing.upperStar Λ f).OplaxMonoidal :=
    (CondensedRing.condensedUpperStarMonoidal Λ f).toOplaxMonoidal
  exact (CondensedRing.upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
```

The existing proved `condensedUpperStarMonoidal_eq` identifies this instance with
the original construction. The comparison is used explicitly in
`canonicalInternalPull_eq`. Each strong instance locally binds the same two
existing invertibility instances before calling the unchanged
`Functor.Monoidal.ofOplaxMonoidal` expression. The resulting maps and inverse
choices are unchanged. Local priority 10 for the two imported condensed
instances avoids competition with the retained item instances; these local
settings do not affect importers. Local irreducibility of the mate and tensor
constructions is restored before the section-unit calculation.

The original `PushNormalized` definition is retained verbatim. Other public
definitions, public signatures, attributes, and public imports are retained.
All added proof helpers are private and proved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | A9 | proof-local changes; same public operations and signatures |
| all importers | unchanged | no public definition or statement change; no adaptation required |

## Status

landed 20261025T041125-L-1010754 2026-10-25 (merge of deliver/A9/Sheaf.Paper.ProEtaleSectionModuleFunctors)
