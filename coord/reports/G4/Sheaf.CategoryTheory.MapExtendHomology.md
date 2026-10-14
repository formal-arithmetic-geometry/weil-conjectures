## What changed

The sandbox proves `mapExtendHomology_nonempty_iso` by mapping
`HomologicalComplex.mapExtendIso` through integer homology and composing with
`extendHomologyIso`. Compared with the current repository, it inlines the two
proof-local `let` bindings `comparison` and `homologyComparison`. The existing
signature, docstring, imports, visibility and definitions are unchanged.
This simplification closes no hole.

## Proved and sorry left

`mapExtendHomology_nonempty_iso` was already proved in the repository. Its node
is `lem-weil-pbc-map-extend-homology`. Holes closed: zero. Holes added: zero.
There are no remaining sorry declarations in this module, and none split off.
The local compile and scratch `#print axioms` check pass; the only axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. The public Mathlib import supplies the homology and extension objects in
the signature and `extendHomologyIso` in the proof. The plain upstream import
supplies `HomologicalComplex.mapExtendIso` only for the proof. The existing
node has no `proof_deps` to remove. No module is pruned.

## Where the brief, the DAG or earlier work was wrong

The dispatcher assigned an already-completed module: no open proof remains
for stage 3. The first report's claim that the copy is unchanged is inaccurate
against the current repository: the difference is the inlining described above.
Its historical X3 review attribution is stale: the current node records B2's
AUTO proof landing on 2026-10-14, with empty `sorry_before` and `sorry_after`.
No statement was changed to manufacture progress.

## Second reading by G4

1. Compared the complete delivered module with the repository using `diff`.
   PASS: the sole difference is inside the proof body, inlining two local let
   bindings. All existing signatures are byte-for-byte identical. No change
   record is needed, and no other module or definition is changed.
2. PASS: compiled the delivered module through `lcompile.py` without errors or
   warnings. A scratch copy with `#print axioms mapExtendHomology_nonempty_iso`
   reports precisely `propext`, `Classical.choice`, and `Quot.sound`. There are
   no sorries, forbidden declarations, or data definitions in this module.
3. PASS: no statements are split off or added, so no new-node searches are
   applicable. Read the actual upstream `mapExtendIso` construction and
   Mathlib `extendHomologyIso`: both construct the required isomorphisms.
   The latter applies whenever the embedding sends q to its integer coercion,
   including q=0, and the argument imposes no exactness assumption on E.
4. PASS: this is the direct existing-library route, composing two isomorphisms.
   Both imports are needed, and the proof-only import is already plain.
   Read `dag/units/sk-thm-p1.json`: this helper is below its realized unit steps;
   the unit route is unchanged. No old proof dependency becomes unnecessary.
5. PASS: the existing node's two proof steps and `proof_origin` describe exactly
   mapExtendIso followed by homologyFunctor.mapIso and extendHomologyIso.
   Its empty `proof_deps` is consistent with these upstream/Mathlib declarations.

Second reading changed only this report, correcting the claimed unchanged copy
and historical review attribution and recording the independent checks. The
Lean proof already present in the sandbox needed no repair.
