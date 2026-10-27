## What changed

Proved
`WeilConjectures.CompactSupportCondensedRealization.systemRestrictionPullInv_isIso`
for the specified ordinary whole-system pullback mate, without quotient flatness.
The canonical pushforward/evaluation comparisons have invertible inverse mates by
their unit equations. A sectionwise identity cube and the mate composition laws
identify the evaluated system mate with the existing fixed-ring scalar pullback
isomorphism. Evaluation and the underlying additive sheaf functors reflect
invertibility, giving the whole-system result.

The generic cube argument is proved in
`Sheaf.Paper.SystemRestrictionInverseMateEvaluation`. Abstract coefficient towers
and local irreducibility avoid repeated unfolding of finite quotient rings and
legacy coefficient-system aliases. The proof imports the existing ringed
restriction comparison and the source library's Mathlib adjunction-mates extension.

The original construction file still exceeded 60 seconds after that optimization.
Profiling identified separate costs in ordinary transport and limit normalization.
`Sheaf.Paper.OrdinaryCompactSupportCoefficientTransport` now contains the ordinary
construction through `systemProjection`, including the closed pullback theorem.
The assigned module publicly re-exports it and retains the strict/derived limit
constructions and `reductionScalar`. All 38 original public signatures match the
original source after whitespace normalization. Existing public names, definition
bodies, attributes, universes and public prerequisites are preserved.

Existing proved support and resolution helpers are isolated in
`Sheaf.Paper.CompactSupportScalarProofs`: the supported-counit inverse-mate
criterion, derived open support, continuous scalar resolution, and the derived
mate resolution criterion. Their proofs retain the previous elaboration settings.
The sectionwise pushforward additivity proof is a public theorem registered only
locally, so the public resolution statement contains no private instance.
The original private `pushforward_additive_explicit` name remains as a proved
wrapper because the native constant-restriction consumer uses it.
No source-library module is modified.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.CompactSupportCondensedRealization.systemRestrictionPullInv_isIso`.
Its attachment is now on
`def-pur-ordinary-compact-support-coefficient-transport` in the re-exported module.

The original hole
`WeilConjectures.CompactSupportCondensedRealization.limitRestriction_existsUnique`
remains unchanged on
`def-pur-semilinear-compact-support-coefficient-transport` in the assigned module.
All three added supporting modules have zero holes. No hole is added or split off;
this is a proof, not a decomposition.

The identity coefficient map, identity scheme map, and zero-module cases use the
same normalized cube. No nonzero, nonempty or flatness hypothesis is introduced.
All four packet modules passed the single-file compiler's 60-second acceptance
check. A source comparison also confirms that all 25 original non-theorem bodies
are textually unchanged. Direct-importer checks used unchanged consumer sources:
`WeilBaseChangeSemilinearPasting` passed. `NativeConstantRestrictionAcyclicity`
elaborated but exceeded the limit (64 seconds against this packet, 67 seconds
against the original published library). `CompactSupportCondensedRealization`
also elaborated but exceeded the limit (70 seconds against this packet, 63 seconds
against the original published library). `CompactSupportRealizationFactorization`
failed at lines 89 and 124 with the same kernel unknown constant
`instEssentiallySmallProfinite_sheaf` against both this packet and the original
published library. These baseline failures are reported for independent review;
no consumer changes are included.

## No longer needed

Removed the assigned file's private imports
`Sheaf.Paper.SemilinearOpenRestrictionSupport` and
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`: their uses moved into
`CompactSupportScalarProofs`, which retains them. The private
`VaryingRingOperations` import is retained by the ordinary construction and its
supporting proofs. Unused private coefficient/push/pull equality helpers are
removed from the assigned file; the support module retains its needed copies.

These dependencies remain needed in the packet. No node or module is pruned or
withdrawn, and the unit `sk-thm-purity-transport` and its route are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The previous node marked the pullback
comparison unfinished. The fixed-ring inverse mate and canonical evaluation unit
equations complete it; derived evaluation faithfulness is unnecessary.

A private additivity instance could not occur in the type of the transferred
public resolution theorem. Its existing sectionwise proof is exposed as a theorem
registered only locally, and the private compatibility wrapper preserves the
native constant-restriction API.

The parent has no resolved imported blueprint ancestor. New nodes preserve the
inherited via chain and name the Step 10 subarguments they serve.

## New nodes

`lem-pur-system-restriction-inverse-mate-evaluation` records the fully proved
coefficient-level inverse-mate cube in
`Sheaf.Paper.SystemRestrictionInverseMateEvaluation`. LeanSearch found the
underlying evaluation and restriction functors; Loogle found the generic mate
composition laws; Mathlib grep and the imported-blueprint search found no exact
coefficient-system statement. Its proof records the canonical evaluation unit
calculation, normalized direct-image cube, mate correspondence and cancellation.

The following nodes attach proved generic subarguments in
`Sheaf.Paper.CompactSupportScalarProofs`:

- `lem-pur-inverse-mate-supported-counit`: cancellation for the inverse mate.
- `lem-pur-derived-scalar-open-support`: derived support from ordinary support.
- `lem-pur-continuous-scalar-resolution`: small-site/model transport of resolutions.
- `lem-pur-derived-mate-resolution-criterion`: derived-unit cancellation on K-injectives.
- `lem-pur-scalar-site-pushforward-additive`: sectionwise additivity.

Each has its precise Lean attachment and complete proof. Mathlib and blueprint
searches found supporting APIs and scheme-specific cases, with no direct
replacement for these existing generic arguments. None adds a hole.

`def-pur-ordinary-compact-support-coefficient-transport` attaches the ordinary
construction from `rightUnitApp` through `systemProjection` to its new module.
The parent attachment retains the limit constructions and `reductionScalar`.
The change record is
`coord/changes/K1-compact-support-coefficient-module-split.md`.
The four direct importers are checked using unchanged temporary copies, which
are removed before delivery. No consumer source change is proposed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
