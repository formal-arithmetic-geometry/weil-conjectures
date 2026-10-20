## What changed

Completed the retirement assigned by `coord/retire-items.tsv`. Withdrew
`Sheaf.Algebra.Homology.OpenRestrictionTensorNatural` in favor of its already
proved upstream twin, and repointed `lem-pc-open-localized-tensor-natural` to
`WeilConjectures.Algebra.Homology.OpenRestrictionTensorNatural`.
Their main theorem signatures are byte-identical.

`OpenRestrictionKFlat` switches its proof import to the upstream twin.
`SliceTensorNatural` receives the four existing public helpers verbatim:
`SheafOfModules.compose_four_squares`, `SheafOfModules.inverse_square`,
`SheafOfModules.tensorObjIsoSheafification_natural`, and
`SheafOfModules.tensor_square`. Its five existing public declarations and all
proof bodies are unchanged. Its proof import becomes the source MonoidalClosed
module, which supplies the tensor-whiskering identities used by one helper.
The slice node's proof records their relocation and drops the irrelevant
open-localized tensor comparison dependency.

Change record: `coord/changes/F4-retire-open-restriction-tensor-natural.md`.
No file under `lean/WeilConjectures/` is changed.

## Proved and sorry left

This is a retirement with zero initial holes. Closed 0 holes, added 0 holes,
split off 0 statements, left 0 holes. The existing proved main theorem
`SheafOfModules.exists_open_localized_tensor_natural` is retained upstream with
its statement and proof unchanged. All four relocated helper proofs remain
complete, as do `SheafOfModules.sliceTensorIso_natural` and
`CochainComplex.open_localized_restriction_isKFlat`.

## No longer needed

Retire `Sheaf.Algebra.Homology.OpenRestrictionTensorNatural`; neither remaining
consumer imports it. Its duplicate main theorem and four private constructions
or naturality proofs are supplied by the unchanged upstream module. The four
public helper declarations are preserved in their sole remaining consumer.

Remove `import Sheaf.Algebra.Homology.OpenRestrictionTensorNatural` from
OpenRestrictionKFlat and SliceTensorNatural. In the former replace it by the
upstream twin; in the latter replace it by MonoidalClosed.

`lem-weil-pbc-slice-tensor-natural` no longer needs
`lem-pc-open-localized-tensor-natural` as a proof dependency: it used only the
four generic helpers. No other declared dependency is pruned; the upstream
open-restriction proof still uses all three original proof dependencies, and
its source declarations and imports are preserved. No blueprint unit route
changes.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed theorem and four earlier splits, but
the current module has no sorry. The live queue and retirement inventory instead
assign duplicate retirement. The upstream main theorem already proves exactly
the required statement, but its four generic helpers are private, so merely
switching all imports would break SliceTensorNatural. Relocating the existing
public helpers resolves that API difference without changing upstream visibility.

The inventory names four consumers; source inspection finds two remaining direct
importers because the other two have already retired. The prior slice proof
record depended on the open-localized comparison only to obtain its helpers;
that dependency is removed to match the relocated declarations.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
