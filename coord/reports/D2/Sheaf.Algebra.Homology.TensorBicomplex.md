## What changed

Repair the ae6f73591 landing rejection by restoring the public names
HomologicalComplex₂.tensorBicomplex and HomologicalComplex₂.tensorBicomplexMap
as the exact transparent abbreviations of Mathlib's bifunctor object and map.
The return explicitly permits keeping the old names. chainTensorMap is unchanged.
Remove the four caller adaptations from the delivery: with the public names
restored, the original callers require no edits. Update the node implementation
plan and declaration list to match the restored compatibility API.
Change record: coord/changes/tensor-bicomplex-mathlib-direct.md.

Validation (2026-10-14): import_prune_check.py exits 0. lcompile.py compiled
all four unmodified downstream modules against the restored item in a scratch
set without errors or warnings. The declaration comparison against the fetched
sheaf-dag base finds no added, removed or changed signatures and no sorry.
The dry run with WEIL_SERVER_COMPILE=1 compiled the item on the project server
and printed OK; the local axiom probe and preflight also passed. deliver3.py
rebases its temporary delivery commit on the fetched origin/sheaf-dag. Nothing
was pushed. The independent second reading remains pending.

## Proved and sorry left

Holes closed: none (0 of 0). Holes added: none. Split off: none.
No sorry remains in the item. This is an interface repair, not proof progress.
All three constructions use existing proved Mathlib operations without new data
chosen from existence theorems.

## No longer needed

None: no imports, modules or dependency nodes are pruned. The restored names
remain necessary to the downstream interface. The four earlier caller adaptations
are withdrawn because they are no longer forced. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery's local notation used the same spelling as the deleted
constants. The textual landing check counted this as continued use of removed
declarations, despite successful compilation. The latest return explicitly
allows retaining the old names; this repair follows that option rather than
claiming that the prior duplicate-removal delivery can land unchanged.
The upstream duplicate-removal request is consequently not claimed complete;
compatibility names are retained to satisfy this landing return. The stale
second-reading section and validation claims were removed for a fresh review.


## Second reading by D2

1. PASS: diffed the only delivered Lean module against the repository version.
   All three existing declaration signatures and bodies are unchanged; no names,
   hypotheses, conclusions, visibility, or imports changed. The Lean diff is
   documentation only. The change record accounts for restoring the API of the
   rejected ae6f73591 delivery; its four caller adaptations are absent.
2. PASS: independently compiled the item using lcompile.py. Explicit #print axioms
   in a scratch copy reports exactly propext, Classical.choice, and Quot.sound for
   HomologicalComplex₂.tensorBicomplex, HomologicalComplex₂.tensorBicomplexMap,
   and HomologicalComplex₂.chainTensorMap. No sorry, axiom, unsafe, opaque,
   implemented_by, extern, or kernel-check bypass occurs. The definitions are
   concrete Mathlib constructions, with no arbitrary unproved existence witness.
3. PASS: no new statements, nodes, or split-off holes. Read Mathlib's
   mapBifunctorHomologicalComplexObj and uncurry: the bicomplex differentials
   tensor the respective differential with the identity, commute by naturality,
   and square to zero by functoriality. The uncurried map composes the two
   variable maps and hence has the required tensor-map components. No new lemma
   duplicates an existing result; no small-case test for a new statement arises.
4. PASS: the construction already takes the direct Mathlib route. All four
   public imports support the exposed constructions, not a proof-only helper.
   No old proof dependency is dropped, so No longer needed correctly says none.
   Read sk-thm-p1.json: this auxiliary node realizes no unit statement or step;
   the unit's realized route stays intact. Independently compiled fresh copies
   of all four original callers against the sandbox item, in import order:
   TensorResolutionColumnCokernelIso, TensorResolutionRowCokernelIso,
   TorSymmetry, and FlatResolutionTorComparison; all passed without warnings.
5. PASS after repair: the proof, proof_deps, and proof_origin describe the
   canonical Mathlib implementation. The two dependencies are existing Mathlib
   matches (termwise complex tensoring and module tensor product). The statement
   and stmt_deps remain unchanged; the declaration list contains all three
   constructions. No new-node requirements apply.

Second reading changed only the node metadata: restored the original primary
lean.declaration HomologicalComplex₂.tensorBicomplex and its matching
lean.statement, rather than redirecting the bicomplex node to chainTensorMap.
No Lean code or change record required repair. Holes closed: 0 of 0; holes added:
0; split off: 0; modules pruned: none. This delivery is an interface-return repair,
not proof progress.
