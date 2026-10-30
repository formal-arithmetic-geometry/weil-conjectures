# Q107 maintenance handoff, 2026-10-17

The repeated failures of `det-sp-tower-exceptional-bc` were provider transport
failures. All eleven completed worker logs from `1792194680` through
`1792196713` ended with `ERROR: exceeded retry limit, last status: 429 Too Many
Requests`, and none wrote `last.txt`. The dispatcher's `NOANSWER: ` is not a
mathematical review or a successful preflight. The dispatcher state reported
10 tries; the eleven historical failed runs are preserved as evidence.

The shared recovery supervisor is installed at
`/home/ubuntu/weil-launcher-all/codex_retry.py` through the existing
`/home/ubuntu/.local/bin/codex` entry point (server commit
`a1a68055f2b73fe62674754cb95071667bd798ac`). New dispatched workers use bounded,
jittered retries and resume the same session when possible. Exhaustion writes
an explicit provider failure to `last.txt`. Inspect the adjacent
`codex-retry.json` and `[codex-retry]` log lines for recovery status. Do not
change the mathematical statement to address a provider error.

Continue the retained sandbox at
`/home/ubuntu/weil-newtargets-sandbox/Q107/det-sp-tower-exceptional-bc`.
It contains an unfinished split, citations and search evidence. Those files
have not been accepted by maintenance. Re-read them against the current DAG
and stage-1 brief; preserve useful work. At maintenance inspection a worker
started before supervisor installation was still editing this sandbox, so
the exact file set can change after this note.

Perform the required server checks using `srvcheck.py` and, after completing
the report and citation audit, run the normal `deliver.py Q107
det-sp-tower-exceptional-bc --no-push .` dry run. A first worker answers READY
only after it passes; the independent second reader then follows its own brief
and delivers. This remains stage 1. Failure counts never make the item
ineligible. Do not delete the sandbox, reset tries, kill the active worker, or
interpret an interrupted tool invocation as completed validation.


---

Re-plan note, 2026-10-29 (owner order; batch 5 follows the CURRENT blueprint).

re-anchor to the current blueprint (owner order 2026-10-29, Zulip #1231; record coord/legacy-coefficient-route-drop-20261029.md): the legacy l-adic coefficient model (rationalization + Karoubi envelope, common-stage pair category, adic/normalized systems) was removed from the blueprint in 6847f52b6 and is withdrawn from our route (coord/route-pivot-dropped.txt). This node's plan cites withdrawn node(s): lem-sp-ctf-tower-pullback-reconstruction, lem-sp-integral-exceptional-mate-transport, lem-sp-tower-mate-evaluation-reduction. Rewrite its proof along the CURRENT blueprint proof (literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.md, and the node's blueprint_update if present), which uses condensed coefficients $\overline{\mathbf Q}_{\ell,X}=p_X^*\underline{\overline{\mathbf Q}_\ell}$. Cite no node listed in coord/route-pivot-dropped.txt. Current blueprint dependencies already in the DAG, to cite as the deps where the proof uses them: det-sp-mixed-base-change, det-sp-tower-gluing, det-sp-tower-shriek-levels, det-sp-integral-adjunction-bijection. Keep this node's statement unless the current blueprint statement differs (blueprint_update.changed has statement); then follow the current blueprint statement. New nodes follow the stage-1 rules (tools/preflight_delivery.py checks 4 and 9): status unsplit with NO proof steps (or status mathlib with an exact mathlib_match), a self-contained TeX statement that cites nodes, source, three kinds of Mathlib search, blueprint.from.node this node, and NO `lean` field. Its proof becomes the assembly of the current-blueprint steps (steps citing the deps above and the new nodes), at most 3000 characters. The Lean of this node is re-proved in stage 3 afterwards (its module is listed as a repair while it still rests on the withdrawn route).
