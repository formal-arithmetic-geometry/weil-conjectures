# Q37 `lem-coef-infinity-relative-cone-constant-test`: provider failure handoff

The five counted failures were infrastructure failures. The first and fourth attempts reached `READY` after completing the split and no-push preflight, but their follow-up/check work was interrupted; the later attempts (including run `1792194097`) ended with terminal Codex HTTP 429 responses (`Too Many Requests`) before writing `last.txt`. The dispatcher therefore recorded the historical `NOANSWER: ` note. There is no matching return, delivery, or landing record for this item, and the retained sandbox has a complete five-step report, citations, and a passed no-push preflight (`7cf55ef9dc`). A fresh resumed run `1792197037` has since completed a new no-push preflight at `ca087b8769` and answered `READY`, confirming that the preserved work is usable once the second-reader check is scheduled. This is not an item statement, module, permission, or mathematics failure.

The shared dispatcher had previously admitted hundreds of provider sessions (the process was started while `total_slots` was 700 and later the configuration was 400), producing a gateway concurrency burst. The installed launcher repair is the cause fix: `/home/ubuntu/weil-launcher-all/dispatch_all.py` uses shared `ProviderCapacity` reservations and classifies transport 429s; `codex_capacity.py` caps and cools admissions after a provider failure; `codex_retry.py` retains the sandbox/session and writes a diagnostic when a final answer cannot be recorded; and `config.json` sets `provider_start_slots: 8` and `provider_cooldown_s: 60`. Source/config backups are retained beside those files. The repair and its regression evidence are recorded by the concurrent Q94 maintenance commits `042c0a86e5f782ffff3ceb27a53921a8796bdf92` and `2fcdbe9f879bfa2ec9a77d7e318104e46472cfad`.

The already-running dispatcher process predates that source repair and was left running so existing sessions could drain; it was not killed or restarted. The adaptive admission activates at the next normal dispatcher start. No Lean source, DAG node, claim, failure counter, or item mathematics was changed for Q37.

This Q37 handoff is the only server project change for this maintenance item. The next worker should resume `/home/ubuntu/weil-newtargets-sandbox/Q37/lem-coef-infinity-relative-cone-constant-test`, inspect the existing successful preflight, and rerun:

```
python3 /home/ubuntu/weil-launcher-nt/deliver.py Q37 lem-coef-infinity-relative-cone-constant-test --no-push
```

after provider admission is available. It should perform the required second reading/check and delivery from the preserved sandbox; it should not redo the split merely because the old state says `NOANSWER`. Failure counts remain dispatch-eligible.
