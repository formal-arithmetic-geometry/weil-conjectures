# NL Roos completeness delivery: repaired coefficient-datum dependency cycle

Maintenance, 2026-10-21. Item: `lem-pur-roos-intrinsic-completeness-equivalence`, stage 2.

Commit `461e0274ffc405dd25a5e3edd03e25a3da23f83d` appended a proof step to
`def-weil-pbc-adic-coefficient-datum`, citing the downstream
`lem-weil-pbc-completed-constant-finite-complex-realization`. The latter depends
back on the coefficient datum through completed-constant-sheaf-reduction, and
also reaches intrinsic-completion through the constant-completion reflector.
The stage-2 gate correctly refused inherited cycles through the touched
intrinsic-completion node. The ordinary worker cannot change dependency edges
of a dependency repair, so repeated dispatch could not fix this live data error.

The appended step uses only the elementary strict quotient-map construction,
not the finite-complex realization assertion. Its `completedConstant_quotients`
helper is implemented privately in CompletedConstantFiniteComplexRealization,
but constructs `CompletedConstantQuotientTower` from the objects and sectionwise
maps defined in CompletedConstantRealizationData. It uses limit projection
naturality and the ring diagram's identity/composition equations. It calls no
finite-complex realization, flatness or completion-reflector theorem. The finite
coefficient comparison separately uses proetale-modules; the K-flat argument
separately uses the existing independent change-of-rings node.

Maintenance replaces this mistaken theorem citation in that step's `uses` and
the node's `proof_deps` with the existing foundational definition node
`def-weil-pbc-completed-constant-realization-data`, and clarifies the step text.
The coefficient datum's statement, statement dependencies and Lean binding are
unchanged. No Lean source, tool or gate is changed; no theorem is proved here.

Next worker: retain the three Lean modules and node records in the saved packet.
Run the prescribed `deliver2.py NL lem-pur-roos-intrinsic-completeness-equivalence
--no-push` against the current server base, then deliver when it passes. The
wrapper preserves current server metadata for dependency nodes and takes only
their `lean` fields, so the old dependency copies need no edge edit. The old
BLOCKED report entries describe the pre-repair base. Do not delete a legitimate
intrinsic-completion or derived-inverse-limit edge or weaken the cycle validator.

Backups (original node bytes and an empty marker for this previously absent note):
`local/maintenance/NL-roos-completeness-1792565872/<relative path>.bak`.
