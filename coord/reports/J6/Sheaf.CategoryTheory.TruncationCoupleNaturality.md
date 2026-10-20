## What changed

Completed the retirement assignment in `coord/retire-items.tsv` for
`Sheaf.CategoryTheory.TruncationCoupleNaturality`. Its adopted twin
`WeilConjectures.CategoryTheory.TruncationCoupleNaturality` already contains the
three explicit definitions and the full raw-naturality proof. Withdraw the duplicate
via `deleted.txt`, migrate the sole consumer's proof import, and reattach node
`lem-pc-raw-truncation-couple-naturality` to the adopted theorem.

The adapted consumer is `Sheaf.CategoryTheory.NaturalTruncationCouple`.
Only its proof import changes; every declaration, signature and proof body stays
verbatim. The three definitions in the retired and adopted modules are textually
identical, as is the displayed signature of `raw_naturality`. The adopted theorem
omits the unused Grothendieck instance on B, which causes no call-site change.
No upstream file or target statement is modified.

Validation: the migrated consumer compiles through `lcompile.py` in 2.6 seconds
without errors or warnings. A separate scratch import checks the adopted
`abutmentMap`, `singleIso`, `homologyMap` and `raw_naturality`; all four use exactly
`propext`, `Classical.choice`, and `Quot.sound`. The import-direction check permits
the new proof import. Declaration bodies and signature text were compared directly.
The consumer's full project import closure replaces exactly the retired copy with
the adopted twin and gains no pair of Sheaf/WeilConjectures duplicates. The delivery
dry run compiles and passes preflight with independent CODEX review required.

Change record: `coord/changes/J6-retire-truncation-couple-naturality.md`.

## Proved and sorry left

This is a retirement repair with zero original holes, not a new proof or a
decomposition. Holes closed: none (0 of 0). Holes added: none. Split-off statements:
none. Remaining holes in the withdrawn module and adapted consumer: none.

The existing theorem `CategoryTheory.TruncationCouple.raw_naturality`
(node `lem-pc-raw-truncation-couple-naturality`) remains fully proved in the adopted
module, as do its three public definitions. No theorem is replaced by a hole.

## No longer needed

Pruned module: `Sheaf.CategoryTheory.TruncationCoupleNaturality`.
Removed its proof import from `Sheaf.CategoryTheory.NaturalTruncationCouple` and
replaced it by the adopted twin's proof import. No other module imports the retired
copy, including in quarantine. The duplicate's private localization, triangle and
bridge helpers are supplied by the existing adopted proof and need no new modules.

No mathematical DAG node or proof dependency is pruned: the parent
`lem-pc-natural-bounded-below-truncation-couples` still needs raw naturality and
continues to cite the same node, whose Lean record now names the adopted module.
The four-step proof plan and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic brief suggests proving holes, but this item is explicitly a zero-hole
retirement row. Its old `lean.module` pointed to a duplicate despite the adopted
source already providing all public names. The prior bulk-retirement record left
it for a later pass because the consumer was busy; the current shared snapshot
has no consumer claim or J6 return. This delivery resolves the outstanding row.

The adopted theorem's fewer hypotheses are an existing upstream improvement;
its construction and all five naturality equations agree with the old theorem.
No mathematical defect or change to the unit's route was needed. LeanFinder and
Loogle searches return the component truncation-naturality lemmas, and project
search finds the exact already-proved adopted theorem, which is the shortest route.

## Forced adaptations

`Sheaf.CategoryTheory.NaturalTruncationCouple`, the sole direct importer, must change
its line 17 when the copy is withdrawn. An isolated counterfactual compiled the
empty retirement stub, then compiled the unmodified original consumer against it.
The original failed in 3.0 seconds with these errors (among their consequences):

```text
NaturalTruncationCouple.lean:78:11: error(lean.unknownIdentifier):
Unknown identifier `TruncationCouple.abutmentMap`
NaturalTruncationCouple.lean:167:4: error(lean.unknownIdentifier):
Unknown identifier `TruncationCouple.singleIso`
NaturalTruncationCouple.lean:178:6: error(lean.unknownIdentifier):
Unknown identifier `TruncationCouple.raw_naturality`
```

The adapted consumer replaces only the line-17 proof import with
`import WeilConjectures.CategoryTheory.TruncationCoupleNaturality` and compiles
cleanly. No declaration, proof body, visibility or public import changes.
The consumer has no claim file in the shared snapshot; the forced migration is
necessary irrespective of its live holder, and the independent reader can repeat
the same counterfactual against the withdrawn stub.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
