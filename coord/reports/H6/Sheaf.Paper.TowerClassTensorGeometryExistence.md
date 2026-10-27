## What changed

`Sheaf.Paper.TowerClassTensorGeometryExistence.exists_tensorGeometry` now assembles
compatible finite unit and tensor comparisons into the required actual system
isomorphisms. Its signature and public import are unchanged. The private helper
`adjoint_evaluation` derives evaluation of every ordinary transpose from the
existing normalized unit equation and naturality of ordinaryPushEvaluation.
`systemHom_ext` proves joint faithfulness of the level evaluations directly on
sequence-site sections. The tensor maps are assembled separately for each pair,
then finite naturality proves naturality of their assembled maps.

Two new modules isolate the unfinished finite constructions:
`Sheaf.Paper.TowerClassUnitLevelCoordinates` selects normalized geometry and
constructs compatible rank-one comparisons; and
`Sheaf.Paper.TowerClassTensorLevelCoordinates` constructs compatible finite tensor
comparisons in that same geometry. Neither asserts the system isomorphism that
the item now constructs. Each has a source, a proof in words, and a new node.
The item node's proof route records these steps, systemIsoOfEvaluation_exists,
and geometry_unit_evaluation. There are no changes to existing definitions,
existing theorem signatures, target statements, or other existing modules.

Validation: both new finite statement modules compiled without warnings in the
latest all-files run (43.6 s and 47.9 s). After correcting the adjunction helper,
the item compiled without warnings in a separate lcompile.py run (22.5 s).
The original signature/public import, 100-character line width, and new-node
Lean signatures were also checked.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.SpTowerClasses.exists_tensorGeometry` by a complete
assembly proof from the finite statements and the existing system-assembly and
unit-evaluation theorems. There are no remaining sorries in the item module.
The two private helpers are proved without new holes.

Added these two named holes, and no others:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_unitLevelCoordinates`, node
  `lem-sfb-tower-class-unit-level-coordinates`.
- `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_tensorLevelCoordinates`, node
  `lem-sfb-tower-class-tensor-level-coordinates`.

This is a decomposition, not a net proof gain: one original hole closed, two
holes added. Existing dependencies with sorries remain dependencies; this packet
does not claim that the original theorem is independent of sorryAx.

## No longer needed

No pre-existing import was removed, and no existing module or declaration is
withdrawn or claimed globally pruned. The original public import
`Sheaf.Paper.TowerClassTensorPullback` stays. Each added proof import is used.

The item node no longer directly depends on
`lem-sp-strict-system-geometric-realization`,
`lem-coef-semilinear-derived-sections`,
`lem-coef-semilinear-ordinary-geometric-realization`, or
`lem-coef-semilinear-geometric-ordinary-tensor`: those constructions belong below
the new finite-coordinate lemmas, whose proof plans still cite them. They are
not globally unnecessary. The item now uses the existing
`lem-coef-system-iso-assembly` instead of duplicating system-isomorphism
construction. The unit's statement and proof route remain intact.

## Where the brief, the DAG or earlier work was wrong

The previous node plan describes canonical ordinary geometry but the existence
of an arbitrary Geometry does not by itself fix all underlying coordinate
comparisons. In particular, levelPushUnderlying can carry a natural automorphism;
level_unit_underlying relates it to the inverse-image comparison. One cannot
assert the normalized finite tensor formula for arbitrary unrelated coordinates.
The first new lemma explicitly chooses the canonical direct-image underlying
comparisons, acting as the identity on all sections. The second uses that
hypothesis, rather than assuming a coefficient-unit normalization alone forces
all tensor normalizations. This is an additional property of the selected
witness, not an added hypothesis of the original theorem.

The remaining work is finite construction and normalization, rather than system
assembly. The new statements account for zero modules, empty charts, n=0, and
identity coefficient transitions. They do not assert flatness of quotient maps.
The finite unit proof uses the unital constant sheaf comparison, which remains
valid on empty charts.

A read-only transitive DAG check also encountered the pre-existing cycle
`lem-pc-ring-hom-extension-differential` ->
`lem-pc-ring-hom-extension-differential-adjacent` ->
`lem-pc-ring-hom-extension-differential`. Neither node was changed. A separate
reachability check confirmed neither new node depends back on the item.

## New nodes

`lem-sfb-tower-class-unit-level-coordinates` is the unit-only finite step of
blueprint operations proof (2), with canonical level direct-image coordinates.
Its quotient-horizontal maps are not yet a system morphism. The item constructs
that morphism and proves its normalization. Its proof plan uses the existing
strict realization, ordinary inverse/direct-system construction with the actual
finite adjunctions supplied, and derived evaluation/tensor completion, followed
by the finite pullbackObjUnitToUnit map and equality of transposes.

`lem-sfb-tower-class-tensor-level-coordinates` is the finite tensor step of the
same clause. It states horizontal compatibility, naturality and the finite
adjoint formula, for geometry already selected by the unit step. Its proof plan
uses the finite part of geometricOrdinaryTensor_exists and the underlying-unit
normalization. The item supplies joint faithfulness, assembly into system
isomorphisms, naturality of the resulting system maps and the ordinary system
adjoint formula. Thus this is a separate part of the argument, not the original
existential statement with a new name.

Both nodes record leanfinder, loogle and grep searches. Those found finite
Mathlib pullback-unit lemmas and the existing local ordinary tensor and system
assembly tools, but no theorem providing these normalized finite coordinates on
the actual quotient tower. Blueprint searches for tensor inverse and coefficient
unit found no identical blueprint statement; both nodes retain the item's
blueprint ancestor and unit. No change record is required: the only existing
module changed is the item, with its existing statement unchanged.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
