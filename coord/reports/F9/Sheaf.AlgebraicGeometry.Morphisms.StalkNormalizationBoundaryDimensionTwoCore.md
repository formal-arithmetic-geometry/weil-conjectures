## What changed

Retired the duplicate
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore`
in favor of its existing `WeilConjectures` twin, as explicitly requested by its
row in `coord/retire-items.tsv` and the human hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`.

The sole direct consumer,
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo`,
now imports the twin and calls
`stalk_normalization_boundary_dimension_two_target c U s hmin hdepth`.
The upstream theorem omits the former unused hS and hs binders. The consumer
retains its complete original signature, including those hypotheses, and its
transfer argument is unchanged. No source-library file is modified.

Repointed `new-stalk-normalization-boundary-dimension-two-target` to the upstream
module, file and exact declaration signature. Its mathematical statement,
proof, dependencies and unit route are unchanged. The depth propagation and
support-dimension proof still uses the same existing upstream lemmas.

Change record:
`coord/changes/F9-retire-stalk-normalization-boundary-dimension-two-core.md`.

## Proved and sorry left

This is a listed retirement repair with zero original holes. No hole was
closed, added or split off. Neither the retired theorem
`AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two_target`
(node `new-stalk-normalization-boundary-dimension-two-target`) nor the adapted
consumer theorem `AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two`
(node `lem-sbc-stalk-normalization-boundary-dimension-two`) has a sorry.
The delivered Lean module has zero holes.

The upstream target theorem was checked with lcompile.py and #print axioms:
only propext, Classical.choice and Quot.sound occur. The adapted consumer
compiled in 6.4 seconds. Its #print axioms and a compile/axiom check of the
unchanged indirect consumer
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_boundary_depths`
also show only those three standard axioms. The complete consumer signature was
compared byte for byte with the original and is unchanged.

The required deliver3.py --no-push dry run passed compilation and server
preflight (commit 424ca92d272; CODEX review, as expected for a retirement and
consumer adaptation).

## No longer needed

Withdrawn:
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore`.
Removed its proof import from its sole direct consumer and replaced it with
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore`.
The old Sheaf declaration is not retained as a wrapper. Its existing node is
preserved and attached to the official theorem. No mathematical dependency or
unit step is removed, and no upstream declaration is removed.

Source searches checked imports and declaration uses throughout both library
roots and quarantine. tools/downstream.py reports the direct consumer above
and the indirect consumer
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths`.
There are no other direct users to adapt.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof, but the current module was
already proved. Its actual queued assignment is the human-approved retirement
row, class DIFFERENT: the twin has removed two unused hypotheses. Replacing
only the import makes the original consumer fail with an application type
mismatch at line 41 (the argument c is expected to be an Opens). Omitting hS
and hs in that application repairs the API difference without changing any
consumer statement. Empty pullbacks and empty U require no added hypotheses;
the official proof handles exactly the same boundary and depth argument.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo`
is unclaimed in the shared claim records. Retirement forces only two edits:
line 10 replaces the proof import with the upstream twin, and line 41 omits
hS and hs from the application of the twin's theorem. Against the upstream
import, the original application failed exactly as follows:

```text
line 41:61: error: Application type mismatch: The argument
  c
has type
  C ⟶ S
but is expected to have type
  Opens ?m.308
in the application
  stalk_normalization_boundary_dimension_two_target ?m.313 c
```

The adapted file compiles. Every existing declaration signature and visibility
is identical; there are no other edits or added helpers in this consumer.
The indirect consumer is unchanged and was separately compiled and axiom-checked
against the sandbox's compiled adapted consumer.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
