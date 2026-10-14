## What changed

Verified the queued upstream-review #1424 duplicate repair against the current
repository and restored sandbox. The item already uses the canonical
`HomologicalComplex.mapExtendIso`; no duplicate `mapExtendTermIso`,
`mapExtendTermIso_comm`, or `mapExtendComplexIso` remains. The proof now makes the two recorded DAG
steps explicit: a locally typed
`comparison` uses the canonical upstream complex isomorphism, and
`homologyComparison` maps it by integer homology before composition. These are
local constructed isomorphisms, not additional declarations or duplicate APIs.
This handoff also refreshes the report after the earlier attempt.

The repair is recorded in `coord/changes/map-extend-homology.md` (landed
20261013T224517-L-1474380). The later direct-public-import pruning is recorded in
`coord/changes/map-extend-homology-import-pruning.md`. No new change record,
statement change, node change, or forced adaptation is necessary.

## Proved and sorry left

`mapExtendHomology_nonempty_iso` is completely proved by applying integer homology
to `HomologicalComplex.mapExtendIso`, then composing with `extendHomologyIso`.
Baseline holes: 0. Holes closed: 0 of 0. Holes added: 0. Split off: 0.
No `sorry` remains. This is verification of a listed repair, not net proof progress.
The public signature, universes, hypotheses, and conclusion are unchanged.

## No longer needed

No additional import, module, or node is pruned relative to the current repository.
The already-landed repair removed the private duplicate constructions
`mapExtendTermIso`, `mapExtendTermIso_comm`, and `mapExtendComplexIso`.
The already-landed pruning removed direct public imports
`Mathlib.Algebra.Homology.Embedding.CochainComplex` and
`Mathlib.Algebra.Homology.HomologicalComplexAbelian`.
The proof needs public `Mathlib.Algebra.Homology.Embedding.ExtendHomology` and
proof-only `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`.
The node has empty `proof_deps`; no planned dependency node is retired.

## Where the brief, the DAG or earlier work was wrong

The repair queue names a duplicate that has already been removed in the current
baseline. The previous ABANDON incorrectly treated this completed repair as an
unprovable stage-3 item; the latest deliver3.py explicitly allows listed repairs
with no baseline holes. The correct action is to verify the canonical proof and
run the repair dry run without inventing sorries or unrelated edits. The first
dry run accepted zero baseline holes but rejected an unchanged item module;
the proof now exposes its existing two-step argument in local bindings.

The node's two recorded proof steps match the Lean term. The auxiliary node is
not among the unit sk-thm-p1's realized steps, and no unit route changes.
The upstream comparison only requires preservation of zero morphisms, supplied
by additivity. Mathlib's embedding homology comparison includes q=0, so no
exactness assumption is needed. Zero complexes and zero additive functors are
covered by the same constructions. The sole direct importer,
`Sheaf.Paper.FreeRepresentableHomotopyHomology`, calls the unchanged public
theorem and needs no adaptation. A repository-wide search found no callers of
the removed private duplicate names.

Verification: the canonical proof compiles with only `propext`,
`Classical.choice`, and `Quot.sound`. The delivery dry run printed OK (pending
independent second reading), and nothing was pushed. An optional single-file
compile of the unchanged direct importer hit its 60-second limit; it did not
produce a compiler error before timing out. No downstream compile success is
claimed. The delivered item compiled in 3.6 seconds with the axiom check.


## Second reading by D4

1. PASS: Compared the sole delivered module with the repository using `diff -u`.
   Only the theorem proof body changes. The entire prefix through the signature is
   byte for byte identical, including universes, hypotheses, conclusion, visibility,
   docstring and imports. The signature also exactly matches the node's Lean record.
   No definition, target, other module, node or change record is delivered.
2. PASS: Independently compiled the delivered module with lcompile.py (1.6 seconds,
   no errors or warnings). Compiled an exact scratch copy with `#print axioms`:
   `mapExtendHomology_nonempty_iso` uses only `propext`, `Classical.choice`,
   `Quot.sound`. Inspected the whole proof and scanned for forbidden declarations;
   no sorry, axiom, unsafe, opaque, extern, implemented_by or kernel-check bypass.
   Both local isomorphisms are constructed from proved canonical isomorphisms;
   no witness is selected from an unproved existence statement.
3. PASS: No split-off statements, new declarations or new nodes. Read the upstream
   construction `HomologicalComplex.mapExtendIso` and Mathlib's
   `extendHomologyIso`: the first needs only preservation of zero morphisms and
   the second requires the embedding index equality, satisfied by rfl for every
   natural q. In particular q=0, the zero complex and the zero additive functor
   require no extra hypothesis. Nothing asserts that an arbitrary additive functor
   preserves homology of the original complex.
4. PASS: The proof uses the existing upstream comparison, maps it by homology,
   and composes with the existing extension homology comparison. A fresh Mathlib
   grep search for `homologyFunctor.*mapIso|mapExtendIso` returned generic mapIso
   examples, no shorter complete result; repository searches confirm canonical
   mapExtendIso usage and no needed duplicate construction. Both direct imports
   are used; ExtendMap is correctly proof-only. No old proof dependency is pruned
   (proof_deps is empty), and no further import is removable. Read sk-thm-p1's
   realized statement and all steps: this auxiliary node is not a realized unit
   step, and the unit route is preserved.
5. PASS: Read lem-weil-pbc-map-extend-homology's statement, Lean record, two proof
   steps, empty proof_deps and proof_origin. They match the delivered proof and
   canonical source declarations exactly. The sandbox dag.json is only a briefing
   snapshot, not a delivered node; its older reviewed_proof metadata is not copied
   into the repository. No new node fields require checking.

Second reading changed only this report by adding the independent review. No
Lean repair was needed. This verifies a queued repair with zero baseline holes:
0 holes closed, 0 holes added, 0 split off, and no newly pruned modules or nodes.
The earlier downstream timeout is not a claimed success and is irrelevant to this
proof-only body change with identical imports and signature.
