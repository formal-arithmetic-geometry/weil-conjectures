## What changed

Added two proof-only modules splitting the outer-column theorem into fixed parity cases:
`PerfectHomMayerVietorisGeometricColumnsEven` and `...Odd`. The original module now
classifies `Fin 5` indices and combines the two strict subcases, using `omega` to exclude
index 2. The two geometric recognition subtheorems remain named `sorry`s with their
DAG nodes.

## Proved and sorry left

The original theorem `AlgebraicGeometry.perfect_hom_mayerVietoris_geometric_columns`
is proved from the two parity-fixed subtheorems. Sorry remains in
`perfect_hom_mayerVietoris_geometric_columns_even` and
`perfect_hom_mayerVietoris_geometric_columns_odd`, each in its own new module and node.

## No longer needed

No original proof dependency was removed. The new main proof uses only the two parity
recognition modules; the imported construction modules remain available to those
subtheorems.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt introduced a definitionally identical restatement. This delivery
splits the argument by parity and leaves the geometric recognition itself as two
strictly narrower intermediate statements, while the combination proof is complete.

## New nodes

`lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even` records recognition for
indices 0 and 3. `lem-pc-perfect-hom-mayer-vietoris-geometric-columns-odd` records
recognition for indices 1 and 4.

## Earlier second reading (a previous round; superseded)

The fixed parity statements are strict subcases of the parent theorem, and the main module combines them by a complete finite-index case split.

## Second reading by H4

1. **Comparison with the repository.** The existing parent declaration has the same
   signature and unchanged statement. The delivered edit adds only proof imports and
   replaces its proof; the two parity modules and nodes are new. No unrelated module
   was changed.
2. **Compilation and proof hygiene.** All sandbox modules compile with `lcompile.py
   --all`. The parent theorem has no `sorry`; the only remaining `sorry`s are the
   two explicitly named parity recognition theorems, each documented and represented
   by its node. No forbidden declarations or hollow definitions were introduced.
3. **Statements and nodes.** The even and odd statements are true strict subcases of
   the parent (indices 0,3 and 1,4 respectively), and retain the exact conclusion
   and hypotheses. Their node statements, Lean declarations, sources, and proof
   metadata agree. No existing Mathlib or library declaration duplicates them.
4. **Route and pruning.** The parent proof performs the complete `Fin 5` split,
   excludes index 2 by arithmetic, and invokes the appropriate fixed-column theorem
   in every remaining case. The unit route is preserved; no original import or
   proof dependency can be removed because the open recognition subtheorems use
   those construction modules.
5. **Axioms and delivery checks.** The local build and stage-3 delivery dry run
   complete successfully. The parent proof uses only the two stated parity
   declarations; the remaining axiom footprint is confined to their named
   `sorry`s, as reported above.

Changed files are the parent proof, the two parity theorem modules, their two DAG
nodes, and this report. No further repair was needed.
