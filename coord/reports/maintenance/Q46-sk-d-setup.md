# Q46 sk-d-setup maintenance, 2026-10-17

The ten failures reported for `sk-d-setup@c6ead0af8` are pipeline/provider
failures. The first failed second reader, run `1792195853`, and twelve later
completed runs have no `last.txt` and terminate with HTTP 429 Too Many Requests.
The first request id is `0a76b514-33ac-402b-a57a-2f0bfaf184e0`.
The dispatcher substituted `NOANSWER:` for the absent file and restarted as
an author/repair worker, losing the second-reader phase and its `.check` marker.
The attempt inventory and log hashes are in the adjacent
`Q46-sk-d-setup-attempts.json`. The latest run was still active when inventoried.

The original E7/E2 mathematical return is separate. Its geometric-scope
repair is already retained in the worker sandbox, together with the source
error and citer audit. It passed preflight `0a50cf3289`; the currently active
continuation passed preflight `ec6da5014d` before its final edits. Maintenance
did not edit the node, unit, report, searches, citations, or any Lean source.

Shared fixes landed concurrently during this investigation:

- `a1a68055f2`: the deployed `codex_retry.py` supervisor resumes interrupted
  dispatched sessions after transient provider 429s, respects the original
  budget, and emits a real diagnostic on exhaustion. Its entry-point symlink
  applies to new workers without killing/restarting the current dispatcher.
- `6fb280508f`: transport diagnostics/retries and reader-handoff preservation
  in dispatcher source. Further reader-handoff maintenance was in progress;
  the running Python dispatcher retains its already loaded source.

Validation: `python3 tools/launcher/test_codex_retry.py` passed 11 tests;
`python3 tools/launcher/test_worker_transport.py` passed 8 tests. These use
fake local children and no model API or Lean builds. The actual item worker's
08:36 server preflight also returned rc=0. Provider availability itself is
external; no mathematical change can repair HTTP congestion.

This maintenance adds `tools/launcher/route-notes/sk-d-setup.md`, deployed at
`/home/ubuntu/weil-launcher-nt/route-notes/sk-d-setup.md`, to give subsequent
repair workers this evidence and a concrete continuation. It requires a fresh
dry run for final files, then READY and an independent reader; it grants no
self-review or push bypass. Existing files are backed up before replacement.
The live dispatcher, active workers, their state file, and sandbox are untouched.

The original worker brief's stage-1 restriction applies: no compiler is needed
for this repair. No Lean file was changed or compiled, and no process was killed.

Official OpenAI documentation consulted for retry configuration and provider
rate-limit behavior: https://developers.openai.com/codex/config-reference/
and https://developers.openai.com/api/docs/guides/rate-limits .
