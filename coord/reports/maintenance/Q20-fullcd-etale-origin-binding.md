# Q20 FullCD étale-origin binding maintenance

The stage-1 worker repeatedly failed preflight with:
`units: sk-prop-sf-fullcd-etale-origin cites sk-prop-sf-finiteness, which its nodes do not reach`.
The worker correctly reaches thm-sc-finite-type-torsion-cd via
lem-sf-etale-direct-image-vanishing and
lem-kun-relative-torsion-direct-image-dimension-bound. That dimension theorem
was stamped sk-prop-sf-cbc from its historical blueprint path, although the
current sk-prop-sf-finiteness statement and fifth proof paragraph explicitly
name it as the finite-type torsion dimension bound. None of the reached nodes
carried that finiteness unit; its complete realization is still pending.

Maintenance corrects the theorem's proof-unit binding to sk-prop-sf-finiteness.
Its source path, blueprint ancestry, statement, proof and Lean interface are
preserved. This does not claim that the entire finiteness/constructibility unit
is realized: it identifies the existing carrier of the dimension clause.

The affected boundary citations are accepted generic tools (SETUP.md, tool
lemmas and the unit route). No proof or dependency is added. The individual
reasons are:

- thm-sc-finite-type-torsion-cd: The finiteness unit's cohomological-dimension paragraph explicitly uses the generic affine d+c bound before its Leray/Zariski reduction; this existing affine theorem retains its historical source unit.
- fin4-lem-fibrewise-cohomological-dimension: Apply the general finite-type torsion cohomological-dimension theorem with c=0 to a geometric fibre, exactly as the existing proof does.
- lem-dg-compact-support-amplitude: Apply the general finite-type torsion cohomological-dimension theorem to the closed support over an algebraically closed residue field; the compactification and closed-support proof are unchanged.
- lem-etale-proper-geometric-point-derived-copowers: The existing copower proof uses the general finite-type torsion cohomological-dimension theorem as its finite-dimensional acyclicity input, without replacing its coproduct argument.

The authoritative live DAG is corrected first, then the side DAG, so periodic
sync cannot restore the stale unit. Backups are adjacent files ending in
`.maint-Q20-fullcd-1792138070.bak`. Both commits use the project's merge lock.
The next worker should keep its reviewed split and key-unit realization, run
the usual deliver.py --no-push, and hand off to its independent second reader.
No mathematical work, Lean edits, compiles or lake build were needed here.
The maintenance workspace REPORT.md records final validation and commit ids.
