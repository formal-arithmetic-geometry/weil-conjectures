## What changed

Decomposed `condensed_tate_realization` into the derived augmentation comparison and
the scalar adjoint of the balanced-power comparison. Its complete Lean proof constructs
the unshifted isomorphism, proves normalization and uniqueness through the adjunction,
and applies the unchanged realization/shift comparison.

Moved the existing constructions and proofs verbatim to public integral-data and
derived-data modules so the two independent comparisons can import them without
a cycle. The item
reexports every original public declaration. No target, definition body or existing
public theorem signature changes. The original integral-comparison hole has its own
node and remains explicitly open. Change record:
`coord/changes/J3-condensed-tate-realization-decomposition.md`.

## Proved and sorry left

Closed the body of
`AlgebraicGeometry.ProEtale.CondensedTateRealization.condensed_tate_realization`
by reduction to two smaller statements. This is a decomposition, not a complete proof
of the mathematical realization: one old hole is closed and two holes are added.

Every hole left (three total):

- `AlgebraicGeometry.ProEtale.CondensedTateRealization.integralComparison_existsUnique`:
  unchanged old hole, relocated to CondensedTateIntegralData; not counted as closed
  or newly added.
- `AlgebraicGeometry.ProEtale.CondensedTateRealization.derivedAugmentation_isIso`:
  new split of the strict-tower/derived-limit argument before scalar extension.
- `AlgebraicGeometry.ProEtale.CondensedTateRealization.scalarBalancedPower_isIso`:
  new split of the K-flat scalar computation before reconstruction.

The private `normalized_iso_of_transpose` is proved completely and its isolated
Mathlib-only compile passed in 1.4 seconds. No new axiom or hollow
definition is introduced. The full five-module compile passed through `lcompile.py`,
including the complete final assembly and both new component statements. The two
new statements retain the unit case d=0, the empty scheme, and ell=2. Neither assumes the conclusion or repackages the entire realization.

Compatibility checks: the cleaned main theorem and unchanged direct consumer
`Sheaf.Paper.CondensedOpenCounitComparisons` compile against the sandbox outputs.
`Sheaf.Paper.CondensedOpenCounitUnits` was also checked: its existing
`CounitNormalized` definition (line 213) fails with kernel error
`unknown constant 'instEssentiallySmallProfinite_sheaf'`. An isolated baseline
sandbox containing only the unchanged consumer, with no delivery artifacts, fails
with the same error at lines 125, 150 and 213. This is a pre-existing consumer
failure, not a forced adaptation caused by this delivery. Its source and archive
are preserved; no unrelated consumer change is delivered.
`Sheaf.Paper.CondensedOpenCounitRealization` likewise fails both with the delivery
and in the isolated unchanged baseline: `generalize` reports a non-type-correct
result at line 89, and the kernel reports the same unknown constant at line 80.
All three full consumer sources were checked; both failures occur independently
of the delivery. Temporary consumer copies have been removed from the packet.
A comparison with the archive verifies all original public signatures, all
non-theorem bodies and every previously proved theorem body are unchanged.

## No longer needed

No mathematical dependency, node, module or unit route is pruned. The main node now
directly uses the two comparison nodes; all of its former geometric, coefficient,
K-flat and tensor dependencies remain below these nodes and the coefficient node.
The old proof imports accompany their original constructions into the data module;
this relocation does not remove their mathematical use or any public reexport.

## Where the brief, the DAG or earlier work was wrong

The item was absent from lean at the start, as the current rework row records; its
quarantined source has been preserved and used. The source was restored by the ongoing
shared run during this session. No withdrawal or empty-module replacement is made.

The item's historical blueprint source names an older proof file absent from the
current blueprint. The current unit proof was read: integral reconstruction and
coefficient transport occur in its Steps 2 and 4. The same existing nine-step local
realization argument is retained in the new nodes, with its Bhatt--Scholze and Stacks
sources; the unit's route is unchanged.

The original monolithic constructions exceeded 60 seconds in two unprofiled runs
(73 and 67 seconds). Profiling located repeated category-instance elaboration,
including a 6.7-second local instance registration. The existing controls on
reducibility were retained and the constructions split into two files, so no
shared definition or external importer must change its unfolding behavior.

## New nodes

- `lem-pur-condensed-tate-integral-comparison`: the existing normalized coefficient-ring
  comparison, now independently attached to the integral-data module. This relocates an
  existing hole; it adds no mathematical assumption.
- `lem-pur-condensed-tate-augmentation-isomorphism`: the original projection-normalized
  derived-limit comparison, before realization.
- `lem-pur-condensed-tate-scalar-power-isomorphism`: the original scalar-extension
  comparison on the encoded integral tensor power, before derived-limit reconstruction.
- `def-pur-condensed-tate-realization-constructions`: the existing derived objects,
  projection maps, balanced maps and shift transport, relocated without new holes.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
