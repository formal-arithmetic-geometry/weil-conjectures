## What changed

Verified upstream review #1424's duplicate repair against the current repository
and the existing sandbox. The repaired module already imports
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap` privately and uses
`HomologicalComplex.mapExtendIso` in `mapExtendHomology_nonempty_iso`.
`mapExtendTermIso`, `mapExtendTermIso_comm`, and `mapExtendComplexIso` are absent
from all library sources. Simplified the public theorem proof to compose the canonical homology image
of `mapExtendIso` directly with `extendHomologyIso`, removing the two local
bindings and their redundant type annotation. This report replaces the earlier
stale-assignment report with the repair verification.

The sandbox module compiles without errors or warnings through `lcompile.py`.
The first worker ran the delivery dry run; delivery is performed after the second reading.

## Proved and sorry left

`mapExtendHomology_nonempty_iso` is already proved: apply degree-q homology to
`HomologicalComplex.mapExtendIso`, then compose with `extendHomologyIso` for
`embeddingUpNat`. The statement includes q = 0 and needs only additivity.
Zero initial holes, zero holes closed by D2, zero added, zero left.
This verifies an existing repair, rather than claiming new proof progress.

## No longer needed

The duplicate private declarations `mapExtendTermIso`, `mapExtendTermIso_comm`,
and `mapExtendComplexIso` were already removed by the landed repair.
No additional imports, nodes, or modules are pruned by D2. Both current imports
are needed. The canonical upstream `mapExtendIso` uses `mapExtendX` internally.

## Where the brief, the DAG or earlier work was wrong

The original proof brief and previous report treated this as an item requiring
closure of a sorry. The current assignment explicitly requests review #1424's
repair, which need not close a hole. That repair is already present in the
repository and sandbox. Its node
`lem-weil-pbc-map-extend-homology` already records the canonical proof route;
`coord/changes/map-extend-homology.md` records removal of the duplicates.
Neither needs another edit: the simplified proof uses exactly the same route.

The only external caller is `Sheaf.Paper.FreeRepresentableHomotopyHomology`,
which calls the unchanged `mapExtendHomology_nonempty_iso`. It never calls the
removed private helpers, so no forced adaptation is necessary. No target,
public signature, definition, or visibility changes in this verification.


## Second reading by D2

1. PASS: Diffed the sole delivered module against the repository version. Only
   the proof body changes: two local bindings are inlined. The existing signature,
   universes, visibility, docstring, and imports are byte for byte unchanged.
   No definition or target is altered; no change record or adaptation is needed.
2. PASS: Compiled the delivered file using lcompile.py, with no errors or warnings.
   Compiled a scratch copy ending in `#print axioms mapExtendHomology_nonempty_iso`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no sorries,
   forbidden declarations, or data chosen from an unproved existence theorem.
3. PASS: No statements are split off or added, and there are no new nodes.
   Independently searched Mathlib with msearch.py grep for
   `mapExtendIso|extendHomologyIso`, and searched lean/Sheaf for these names and
   the retired helper names. Read the canonical upstream mapExtendIso construction
   and Mathlib's extendHomologyIso. The proof composes these existing constructions.
   At q=0 the missing predecessor becomes zero; for positive q the embedding
   preserves adjacent degrees. The zero complex and zero additive functor pose
   no extra assumptions. No exactness of the functor is needed.
4. PASS: The route is already the direct composition of the canonical complex
   isomorphism mapped by homology with extension's homology isomorphism. Both
   imports are used; ExtendMap is correctly private because only the proof needs
   it. No old proof-dependency nodes are pruned (`proof_deps` is empty), and no
   modules or imports are newly pruned. Read sk-thm-p1.json and its realized
   steps: this auxiliary comparison changes no unit statement or step and
   bypasses none of its required nodes.
5. PASS: Read lem-weil-pbc-map-extend-homology.json. Its Lean statement matches
   the unchanged signature, and its proof and proof_origin describe exactly
   mapExtendIso, homologyFunctor.mapIso, and extendHomologyIso. Its empty
   proof_deps correctly reflects the use of existing upstream/Mathlib facts
   rather than additional DAG nodes. No node edits are required.

Second reading changed only this report: recorded independent checks and clarified
that the first worker had not pushed. The submitted Lean proof needs no repair.
The sole theorem is fully proved, but was already proved in the baseline:
zero holes closed, zero holes added, zero split off; this is repair verification,
not new proof progress.
