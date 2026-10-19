# Q31 / thm-sf-ctf-stability maintenance, 2026-10-16

The repeated stage-1 failures were caused by missing DAG realization metadata,
not the item's mathematics. `sk-thm-sf-ctf-stability` cites the node-less setting
sketch `sk-def-sf-setting`. The setting sketch had an empty `realized.statement`
and no node stamped with its unit, so realizing the item's own unit made
`tools/units.py` report:

```
units: sk-thm-sf-ctf-stability cites sk-def-sf-setting, which its nodes do not reach
```

The existing definitions have other source units. Adding citations alone could
not make the sketch reachable without its explicit binding. `deliver.py` permits
workers to change only their item's own unit realization; its rejection of the
setting-unit edit was the expected scope boundary. Failure counts remained
history and did not stop dispatch.

During this investigation concurrent NS / prop-sf-open-closed-triangle-all-stages
maintenance installed the shared repair. This task's guarded edit found the
binding already present and made no competing metadata change. The repair changes
only `realized` and `realized_by` in `dag/units/sk-def-sf-setting.json`, binding its
statement to these existing definitions, with an empty proof-step list:

- `def-weil-finite-field-fiber`
- `def-weil-l-adic-coefficient-extension`
- `def-weil-finite-torsion-constructibility`
- `def-weil-finite-tor-amplitude`
- `def-weil-constructible-intervals`
- `def-coefficient-twists-detailed`
- `def-weil-scheme-morphism-properties`

The authoritative live commit is
`97c8bf06c1681962257d065c3c3c2e25894f8006` in
`/home/ubuntu/weil-conjectures-sheaf` (`sheaf-dag`); the side-project commit is
`291ce2369d1a27171b88b5f423193d22953265d4` in
`/home/ubuntu/weil-newtargets` (`newtargets-dag`). Both also record the repair in
`coord/ledger.md`. Original unit records and ledgers are preserved in both
projects as `<path>.maint-NS-setting-1792120017.bak`.

Q31 maintenance independently verified that both committed bindings match, only
the two realization fields differ from the unit backups, and all seven carriers
are direct `stmt_deps` of Q31's retained sandbox item. Its sandbox contains only
the permitted own-unit file, `dag/units/sk-thm-sf-ctf-stability.json`.

The real delivery command completed with exit status 0:

```
python3 /home/ubuntu/weil-launcher-nt/deliver.py Q31 thm-sf-ctf-stability --no-push
OK (not pushed) deliver/Q31/thm-sf-ctf-stability at 4c4b587d4b: preflight passed
```

Full output is
`/home/ubuntu/weil-launcher-all/maint/Q31-thm-sf-ctf-stability-1792120149/dryrun-after-setting.log`
on the launcher machine. The dispatcher subsequently showed the item assigned to
a stage-1 `check` worker in `thm-sf-ctf-stability.1792120650`, with its historical
failure count retained at 6.

The next worker should use the refreshed base and continue normal second reading
and delivery of the retained split. Keep the setting binding in the server/base
metadata; do not add a cross-unit unit file to the sandbox or restamp the existing
definitions. The old BLOCKED log entries describe the pre-repair base. Rerun the
ordinary dry run after any subsequent source/citation changes, then use the
normal reviewed delivery path. Passing preflight is a mechanical validation; the
item's mathematical review remains the second reader's work. This maintenance
changed no Lean file and ran no compiler or Lake build, killed no process, and
did not modify dispatcher state or push the item delivery.
