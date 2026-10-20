# AlgebraicGeometry.relativeMV_resolved_roof_open_mate_comparisons

## Reason

Restore the complete module from the quarantine archive named in `coord/rework.tsv`.
Its recorded duplicate-import failure has been resolved by the current dependencies.
The archive now fails at its local irreducibility command:
`failed to set [local irreducible], derivedPullback is currently [irreducible]`.
The upstream declaration now uses `irreducible_def`.

Removing that redundant entry restores compilation, but the first delivery attempt
exceeded the unchanged 60-second file limit. Profiling showed repeated comparisons
of local row aliases with the expanded expressions in the imported comparisons.

## Old

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  derivedPullback DerivedCategory.Qh RingedSpace.moduleDirectImage
```

The proof destructured the two existence results and transported the numerator
and denominator equations after substituting the concrete fixed resolutions.
Its private helper was `component_roof_transport`.

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh RingedSpace.moduleDirectImage
```

The proof reduces the local row aliases with projection reduction disabled.
Four proved private helpers provide the component and assembly API:

- `map_third_roof_transport` maps a third-component equation and composes a fixed tail.
- `roof_denominator_third` calculates the component for arbitrary short complexes and functors.
- `roof_denominator_transport` transports a roof along an equality of invertible denominators.
- `combine_component_comparisons` assembles the two existential comparisons.

The denominator equation now transports its isomorphism hypothesis explicitly
with `Eq.mp`, avoiding a costly rewrite search between composed row presentations.
`Iso.symm_hom` puts the square comparison in the form expected by the one-open
lemma. The existing denominator-isomorphism proofs are supplied explicitly. Comparison
and transport proofs are passed directly to the assembly lemmas, avoiding
redundant intermediate proof types.
The proof still combines the middle comparison with the one-open comparison for
`U ⊓ V`; it adds no mathematical dependency or assumption.

The public theorem statement, its docstring and all five imports are textually
unchanged. The heartbeat bound is reduced from 1000000 to the verified 100000; the
60-second file deadline is unchanged. No data definition,
source-library declaration, target, public signature or imported environment is
changed. The archive and repair both have zero holes. There are no new axioms.

## Users

The downstream search reports zero live downstream modules and theorem uses.
The sole archived direct consumer applies the identical public statement at
lines 242--243. Its interface needs no adaptation. The quarantine archive and
all dependencies are preserved; no file is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons | N4 | Restore the module and repair local reducibility and proof elaboration. |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMateComparisons | unclaimed in shared snapshot (quarantined) | Public statement and imports are unchanged; no adaptation. |

## Status

landed 20261020T211806-L-3502677 2026-10-20 (merge of deliver/N4/Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons)
