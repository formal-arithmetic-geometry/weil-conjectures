# Q126 maintenance: infinity monadic bar

The repeated BLOCKED answers were caused by missing statement-dependency edges,
not failed mathematics or a compiler/permission failure. The queue correctly
tested the recorded edges, but the item recorded only simplicial sets and
enhanced diagrams/cones. Its statement also uses the nonsymmetric monoidal
infinity-category of endofunctors, coherent monads, and the coherent module
infinity-category `Alg_T(C)`. The landed enhanced-diagram declarations provide
none of those interfaces. Workers correctly obeyed the later bottom-up brief
and could not state other existing DAG nodes in this delivery.

The repair adds these statement edges in both server repositories,
`/home/ubuntu/weil-conjectures-sheaf` (authoritative DAG) and
`/home/ubuntu/weil-newtargets` (isolated stage-2 project):

- `lem-coef-infinity-monadic-bar` -> `def-coef-monoidal-infinity-category`;
- `lem-coef-infinity-monadic-bar` -> `lem-coef-infinity-free-module-bar`;
- `lem-coef-infinity-free-module-bar` -> `def-coef-monoidal-infinity-category`.

The free-module node explicitly introduces the general coherent monad, its
module infinity-category and forgetful functor. Its *interface* is needed to
type this item's comparison target. This edge does not require its proof to
be finished: a stage-2 theorem may still have `sorry`. The remaining proof
dependencies stay proof-only. Fibrations are already a transitive statement
prerequisite of the monoidal definition; no extra direct fibration edge is
needed. The free-module node is still a stage-1 assignment until its split
lands. Its independent split was already in progress in group Q98 when this
maintenance began. Preserve the added monoidal edge when rebasing that split.

Each existing changed node has an adjacent
`.maint-Q126-monadic-bar-1792181210.bak` containing its complete pre-edit text.
Only `stmt_deps` changes: mathematical statements, proofs, proof dependencies,
status, review records and Lean records are preserved. No declaration is
fabricated and no Lean source changes. No Lean compilation or global build
is appropriate for this metadata-only repair. Failure counts and process
lifecycle are untouched. The existing queue and dispatcher's held-claim check
now have the edges needed to enforce bottom-up readiness. The live copy is
also repaired so normal synchronization retains the correction.

## Next worker

Use a fresh node copy from the current shared repository once the statement
prerequisites have usable landed declarations. Use the actual recorded module
and declaration names, not the candidate names from earlier `--source` probes.
Read the monoidal and free-module declarations in full, including the module
category and forgetful functor. Reuse their fully coherent interfaces; the
ordinary Mathlib `Monad.Algebra` is not a replacement for coherent modules in
an arbitrary quasicategory.

The previous Q126 sandbox contained only searches and a cumulative BLOCKED
report, with no Lean file or node binding to recover. The maintenance workspace
preserves that report in `evidence/worker-report-before.md`. The dispatcher may
clean the old sandbox after the item becomes ineligible. Begin from the fresh
base when it resumes. Preserve all mapping-space, coherent composition,
naturality, face/degeneracy, augmentation and splitting clauses. Compile each
eventual Lean file individually with `tools/lean_file.sh` through the prescribed
worker wrapper, at most 60 seconds, and run the normal delivery dry run.

Maintenance claims a dependency-metadata repair, not a completed formalization.
