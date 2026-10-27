## What changed

Proved `WeilConjectures.CompactSupportCondensedRealization.restrictionTower_existsUnique`
in `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport`.
The proof first uses `SemilinearSections.restrictionEvaluation_existsUnique` and the
residue characterization of `completedCoefficientMap` to construct the normalized
comparison at each level. It assembles those comparisons into an isomorphism of
strict towers using the actual transition formulas. Sectionwise identity proves
both normalization and uniqueness. A generic categorical assembly helper retains
its component equations, so normalization does not unfold the nested natural
isomorphism construction. All auxiliary theorems are private and proved.

No public signatures, definitions, or DAG attachments change. Removed the unused
public import `Sheaf.Paper.BoundedConstructibleTower`; no declaration in this file
uses it. The downstream tool lists zero current Lean importers, so no consumer
adaptation is required. The import change is recorded in
`coord/changes/F1-semilinear-compact-support-import-pruning.md`. Local
irreducibility settings keep elaboration from unfolding the chosen sheafification
and coefficient-system constructions. The evaluation API applications explicitly fix their universes. Canonical
functors are kept locally irreducible after the coefficient constructions.
The returned delivery at `8018cd0f700` duplicated the private `normalized_square`
theorem of `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`. This repair adds
`import all Sheaf.SixFunctors.SemilinearProperOpenMatePasting`, removes the duplicate
private `tower_normalized_square`, and uses the existing theorem directly in
`restrictionTower_existsUnique`. The existing public import stays in place.
The repair changes only the proof implementation and private proof access.
Additional local irreducibility settings seal the chosen scalar data, standard
derived localization, completed coefficient ring, support comparison, and limit
comparison while their equation interfaces are used. Elaboration respects these
settings; the existing `systemRestrictionPull` definition retains its original
transparency options locally. No definition body or public signature changes.

## Proved and sorry left

Closed 1 of the 5 original holes:
`WeilConjectures.CompactSupportCondensedRealization.restrictionTower_existsUnique`.
Added 0 holes; split off 0 statements.

The four original holes remain unchanged, all attached to
`def-pur-semilinear-compact-support-coefficient-transport`:

- `WeilConjectures.CompactSupportCondensedRealization.systemRestrictionPullInv_isIso`
- `WeilConjectures.CompactSupportCondensedRealization.systemRestrictionPush_isIso`
- `WeilConjectures.CompactSupportCondensedRealization.systemRestrictionOpenInv_isIso`
- `WeilConjectures.CompactSupportCondensedRealization.limitRestriction_existsUnique`

The repaired item compiled successfully on the project server through
`LCOMPILE_NO_LOCAL=1 python3 /home/ubuntu/weil-launcher/lcompile.py` in 54.3 seconds,
with no errors or warnings. The source duplicate check passed. Delivery performs
the final compile and preflight checks. The four remaining holes are pre-existing
and this repair adds none.

## No longer needed

The duplicate private helper `tower_normalized_square` is removed in favor of the
existing `normalized_square`. Removed the unused import
`Sheaf.Paper.BoundedConstructibleTower`. No node or module is withdrawn. The proof uses the existing
semilinear evaluation and coefficient-sequence interfaces and follows the unit's
strict-tower route. The geometric-mate and derived-limit declarations remain
needed by the public constructions and retain their original holes.

## Where the brief, the DAG or earlier work was wrong

The previous packet missed an identical private theorem in an already imported
module. The return is repaired by importing and applying that existing theorem.
No statement discrepancy was found. This is a partial proof delivery, not a
decomposition: the four geometric and derived-limit holes were not closed.
The completed proof uses identity maps on underlying sections before deriving;
it does not infer equality of derived arrows from their finite evaluations.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
