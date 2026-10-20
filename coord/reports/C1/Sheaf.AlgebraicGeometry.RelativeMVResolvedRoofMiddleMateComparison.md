## What changed

Restored the full module from the quarantine path recorded in `coord/rework.tsv`.
Removed `derivedPullback` from its local irreducibility command because the
upstream declaration is already globally irreducible. The original reproduces
the assigned error through `lcompile.py` in 48.8 seconds of compiler time.
Also replaced four propositional `haveI` bindings by `have` and removed one
unused simp argument to clear the compiler's proof lint warnings.

The theorem statement, existing proof argument, docstrings and all five imports
are preserved. The proof still uses the two one-open roof comparisons, the
invertibility of diagonal components, and the biproduct roof and mate identities.
Change record:
`coord/changes/C1-relative-mv-resolved-roof-middle-reducibility.md`.

Validation: the repaired full module compiles through `lcompile.py` in 48.2
seconds, exit code 0, with no warnings. A textual check confirms the theorem
signature and imports exactly match the archive, there are zero `sorry` tokens,
and all Lean lines have at most 100 characters. `tools/downstream.py` reports
zero live downstream modules and zero live uses of the theorem.

## Proved and sorry left

The archived module contains zero `sorry`s, and the restored module contains zero.
`AlgebraicGeometry.relativeMV_resolved_roof_middle_mate_comparison` retains its
complete proof. Holes closed: none (0 of 0). Holes added: none. No statement is
split off. This delivery repairs compilation rather than claiming a new proof.

## No longer needed

Only the redundant local irreducibility entry for `derivedPullback` and an unused
`Category.assoc` simp argument. No import, node, module, declaration or dependency
is removed. The quarantined direct consumer
`Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons` still uses
the theorem with its identical signature; no adaptation is needed.

## Where the brief, the DAG or earlier work was wrong

This is an assigned zero-hole compile repair, not an unproved theorem: its
archived proof is already complete. The old local attribute command became
invalid after the upstream `derivedPullback` changed to `irreducible_def`.

Searching this snapshot's `dag/nodes` by module name, theorem name and blueprint
tag finds no matching node for
`lem-pc-relative-mv-resolved-roof-middle-mate-comparison`. The archived blueprint
tag and all Lean dependencies are preserved. No DAG metadata or route is changed.
There is no matching current C1 return entry in the local snapshot.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
