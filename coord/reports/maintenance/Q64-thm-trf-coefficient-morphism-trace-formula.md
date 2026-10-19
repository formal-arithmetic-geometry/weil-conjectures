# Q64 maintenance report: thm-trf-coefficient-morphism-trace-formula

Date: 2026-10-17

## Cause

The ten failures were repeated provider HTTP 429 interruptions. The initial author run completed its stage-1 split and no-push preflight (`READY` in run `thm-trf-coefficient-morphism-trace-formula.1792190607`). The subsequent attempts ended before writing `last.txt`; their logs contain `ERROR: exceeded retry limit, last status: 429 Too Many Requests` and request IDs. The old dispatcher treated the missing final answer as empty `NOANSWER`, counted it, and relaunched the item without preserving the intended reader handoff. There is no evidence of a theorem, DAG record, Lean permission, or sandbox data defect.

## Changes

- Added `tools/launcher/route-notes/thm-trf-coefficient-morphism-trace-formula.md` with the preserved sandbox path, transport diagnosis, and exact reader handoff.
- Added this report and matching `.bak` copies for both new files.
- The shared launcher fixes already present in the server history are `6fb280508f` (worker transport/handoff recovery), `a1a68055f2` (provider 429 retry supervisor), and `0abb765411` (reader report retention), followed by later dispatcher recovery commits. No Lean source or theorem record was changed.

## Next worker

Inspect the newest run and retain `/home/ubuntu/weil-newtargets-sandbox/Q64/thm-trf-coefficient-morphism-trace-formula`. Complete the independent reader report, run the existing no-push preflight, and deliver after the reader reaches a final answer. Treat another 429 as transport recovery work and preserve the sandbox.
