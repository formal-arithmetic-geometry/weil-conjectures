## What changed

Replaced the sorry in
`WeilConjectures.PodReindexingCoherence.derived_shift_model` by a complete proof
pasting separate source- and target-shift squares. The private, fully proved
`paste_shift_squares` lemma combines two squares through functoriality,
naturality of `commShiftIso`, naturality of `shiftFunctorAdd'`, and the addition
coherence law for a functor commuting with shifts. The concrete proof factors
the two-input Hom map and uses naturality of the existing source-shift
isomorphism to put the component squares into this form.

Added proof imports of `Sheaf.Paper.PodReindexingDerivedSourceShift` and
`Sheaf.Paper.PodReindexingDerivedTargetShift`. These new modules contain the two
independent one-variable compatibility statements. Each uses the existing
normalized shift, with no new shift definitions or arbitrary choices. The item
keeps its public imports, `derivedShiftEquation` definition and theorem type
unchanged. A scoped unused-variable linter setting accommodates the original
redundant quantified K-injectivity binder; the proof works for all derived
objects from the component squares.

The item compiled without warnings in 12.0 seconds; both new modules compiled
individually in under seven seconds. No existing module besides the item is
changed, so no consumer adaptation is needed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PodReindexingCoherence.derived_shift_model`
(node `lem-pod-reindexing-shift-derived-model`). The private pasting lemma has
a complete proof.

Added two holes, each in a new module:

- `WeilConjectures.PodReindexingCoherence.derived_source_shift_square`, node
  `lem-pod-reindexing-derived-source-shift`, in
  `Sheaf.Paper.PodReindexingDerivedSourceShift`.
- `WeilConjectures.PodReindexingCoherence.derived_target_shift_square`, node
  `lem-pod-reindexing-derived-target-shift`, in
  `Sheaf.Paper.PodReindexingDerivedTargetShift`.

This is a decomposition: one original hole closed and two strictly smaller,
independent one-variable obligations added, for a net increase of one hole.
There are zero sorries in the item module and no new definitions. Neither
remaining theorem restates the double-shift equation or assumes it under a
new name. Each contains just one input shift; the real combination of their
conclusions is proved in the item module.

## No longer needed

No original import or declared dependency is removed. The existing
`Sheaf.Paper.PodReindexingCoherenceData` dependency remains. No module or DAG
node is withdrawn or claimed as globally pruned.

The representative proof does not import the separate chain-shift presentation
and chain-square modules: each remaining one-variable obligation states the
normalization calculation directly for the existing source or target shift.
Those chain modules remain needed by the separate chain field of the parent
`ShiftLaws`, so this delivery does not prune them.

## Where the brief, the DAG or earlier work was wrong

The original single proof step concealed both one-variable normalization
calculations and their formal combination. The updated node records these as
two independent steps and the actual pasting proof. No assertion about a
broken tool or a false mathematical statement is made. The original theorem
and all of its universes and hypotheses are preserved.

The new statements include arbitrary positive, zero and negative integer shifts,
zero objects and empty schemes; neither adds a boundedness or nonemptiness
hypothesis. At zero shift each is the ordinary naturality square, and the sign
in the source calculation is precisely the existing `LeftNormalization` sign.
The target calculation uses the unsigned `RightNormalization`. The source is
represented by the standard localization and the target by a K-injective
resolution, as in the original node. The unit and chapter routes are retained.

## New nodes

`lem-pod-reindexing-derived-source-shift` isolates the signed source-input square
with the existing `sourceShift`. Its source and complete intended projection and
localization argument are in the theorem docstring and node.

`lem-pod-reindexing-derived-target-shift` isolates the unsigned target-input square
with the existing normalized `homCommShift`. Its source and complete intended
projection and localization argument are in the theorem docstring and node.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingDerivedSourceShift": "35c2b5afac76cb13db4ac711c1e061a4c4b60341", "Sheaf.Paper.PodReindexingDerivedTargetShift": "99347fcddccccdbf764d394df084b32c38e0b9fd", "Sheaf.Paper.PodReindexingShiftDerivedModel": "49de223704d88b49c08ecadafa6f3dad71ee78fb"}, "results": {"Sheaf.Paper.PodReindexingShiftDerivedDescent": {"hash": "8e64e475ec8cd24d0c528d40342d7e822fca6dbd", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T10:41:51+0800", "transitive": 0, "version": 1}
```

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
