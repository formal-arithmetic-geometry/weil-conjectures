# Q65 evaluation-definition ownership maintenance

The returned item `lem-trf-graded-pushforward-etale-restriction`, head
`0982992948d1`, requires the plain evaluation and tensor-power definitions to
have a definition-node owner. The retained repair already extracts them, but
the stage-2 delivery reader drops the required companion theorem node as outside
the item's prerequisite closure, then rejects its module as unowned.

This maintenance lands that mechanical extraction before the item is delivered:

- `def-trf-etale-module-evaluation-tensor-powers` owns its module and the eight
  existing declaration names. Its constructions are the existing definitions.
- `GradedEvaluationZariskiEtaleComparison.lean` publicly imports that module and
  removes those declarations. The theorem node's `lean.declarations` reflects
  the new ownership, and its `stmt_deps` cites the definition node it now uses.
- All existing theorem signatures are preserved. The retained worker's explicit
  identity/composition proofs for `evaluationSchemeEtale` replace default
  automation; object and morphism data are unchanged. The extracted monoidal
  instance uses the worker's priority 100 to prevent unrelated instance searches
  from unfolding the small-site model.

The dispatched item's Lean statement is left for the ordinary delivery and
independent review. It can cite the landed definition node without citing the
companion theorem. No artificial dependency on that theorem is introduced.

Validation uses the standard `tools/land_set.sh` path, compiling each of the two
files separately through `tools/lean_file.sh` with the 60-second limit and
registering an interface landing. Original files have adjacent maintenance
`.bak` copies. The server commit is made under `coord/.merge.lock` with the
required Bin Wu identity.

The general protected-tool fix is still needed in `tools/stage2_delivery.py`:
after reporting an advisory prerequisite-closure mismatch, retain the companion
node for ownership checks instead of executing `continue`. This maintenance
does not modify that reader, other landing tools, or launcher policy.
