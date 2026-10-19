# Q55 maintenance: `sk-lem-induction`

## Cause

The repeated failures were provider transport failures. The first two workers
completed the attachment review, but the server correctly refused the proposed
attachment `AlgebraicGeometry.Etale.UniversalBaseChangeProperty.of_forall_lt`
because eleven reachable declarations still contain `sorry`. The later
attempts did not reach a mathematical conclusion: runs
`1792194021`, `1792196095`, `1792196281`, `1792196320`, `1792196369`,
`1792196408`, `1792196564`, `1792196635`, `1792196713`, `1792196772`,
`1792196923`, and `1792197005` end with terminal `429 Too Many Requests`
errors and no `last.txt` answer. The dispatcher reduced each to `NOANSWER: `
and immediately launched another session, so the note concealed the actual
failure and the interrupted reader/work packet was repeatedly lost.

This was systemic provider saturation. The old dispatcher allowed hundreds of
workers against one provider endpoint while its configured global ceiling was
400/700, and it had no shared admission pool for workers, maintenance jobs,
and second readers. The retained packet itself is healthy: the author run
passed `check_dag`, `review_split`, and delivery preflight, and the sandbox now
has a durable stage-1 receipt at head `30b36bf9cc`.

## Repair

The shared launcher repair is installed locally and preserved with backups:

- `/home/ubuntu/weil-launcher-all/dispatch_all.py` now uses adaptive
  `ProviderCapacity` admission for every launch path, classifies terminal 429s,
  preserves pending requests and exact reader roles, and recovers a completed
  stage-1 preflight from `.stage1-ready.json`.
- `/home/ubuntu/weil-launcher-all/codex_capacity.py` supplies the shared,
  cooldown-based admission and 429 diagnostic. Its previous version is
  `/home/ubuntu/weil-launcher-all/codex_capacity.py.bak-Q55-provider-1792196769`.
- `/home/ubuntu/weil-launcher-all/config.json` has
  `provider_start_slots: 8` and `provider_cooldown_s: 60`; the prior
  configuration is retained at
  `/home/ubuntu/weil-launcher-all/config.json.bak-Q94-rate-limit-1792197035`.
- The explicit-session retry and worker-transport paths preserve the sandbox
  and retry the same role after a transient 429. The dispatch source backup is
  `/home/ubuntu/weil-launcher-all/dispatch_all.py.bak-Q55-provider-1792196769`.
- `/home/ubuntu/weil-launcher-nt/route-notes/sk-lem-induction.md` records the
  receipt-backed handoff for the next author and independent reader.

The corresponding server-side launcher infrastructure is already in these
Bin Wu commits on `newtargets-dag`: `ecbefbec53` (shared provider capacity),
`6fb280508f` (worker transport retry), `f2419b5883` (durable stage-1 receipt),
and `a5ae0952c3` (explicit Codex resume retry). This maintenance record and
the item route note were committed under `coord/.merge.lock` in
`c6546f6ba45a5d641fbfcfabb0dc1498f753858f` (`Record Q55 sk-lem-induction
provider repair`).

No DAG record, Lean module, claim, failure counter, or item mathematics was
changed. The running dispatcher (PID 2532170) predates the latest launcher
source/configuration and was left running; no process was killed or restarted.
The adaptive cap takes effect on its next natural start.

## Validation

The repaired local source passes `py_compile`. The relevant regression suites
pass: 36 tests covering provider admission, failure classification, reader
handoff, stage-1 receipts, and state migration; 14 explicit-session Codex retry
tests; 8 worker-transport tests; and 6 no-answer classification tests. A direct
capacity smoke test confirms an initial limit of 8, halves to 4 after a 429,
and cools launches for 60 seconds. The sandbox receipt fingerprint validates
all nine recorded inputs. No Lean compiler or Lake build was run because this
was a launcher/provider failure.

## Next worker

Continue from `/home/ubuntu/weil-newtargets-sandbox/Q55/sk-lem-induction/`.
Run `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q55 sk-lem-induction
--no-push .`, answer `READY sk-lem-induction: 0 new nodes, 0 Mathlib leaves`
when it passes, and let the dispatcher assign the independent second reader.
That reader should append `## Second reading by Q55`, rerun the dry run, and
deliver. Do not attach the refused theorem: its reachable sorry declarations
are an established server audit result. Do not redo the split merely because
the historical state note is `NOANSWER:`.
