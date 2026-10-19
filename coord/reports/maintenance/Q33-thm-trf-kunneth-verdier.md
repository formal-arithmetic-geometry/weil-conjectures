# Q33 thm-trf-kunneth-verdier maintenance, 2026-10-17

The return on delivery e2d451d154 was legitimate: the statement of
def-trf-admissibility changed after review. The retained sandbox contains
the substantive citation/proof-step repair and passed server dry runs
a4ab8a5012 and daffa65503. Do not discard it or restore the old citation.

The repeated empty NOANSWER failures are model transport failures, not
mathematical counterexamples or Lean failures. All twelve completed repair
attempts after the delivered version ended with Codex HTTP 429 errors;
the ten counted failures are the later retry burst. The first maintenance
run at 1792196670 also died with HTTP 429 before investigating. The original
dispatcher read only last.txt, losing both the diagnostic and a successful
dry-run handoff when the model failed before its final answer. Repeated
repairs re-read the same finished split instead of reaching a second reader.

The launcher fix persists a content-checked dry-run receipt and lets a
missing-answer first worker hand off to an independent reader. Changed
inputs, stale rounds, other stages and readers are rejected. It does not
push, merge, change the item mathematics or change failure-count eligibility.
Existing transport/admission changes by other maintenance sessions are
preserved. See tools/launcher/README.md for deployment and the recovery
bridge for an already-running dispatcher.

Next worker: retain the repaired sandbox, read the current cited statements
and sources, finish the independent second reading, then use the normal
delivery tool. The old e2d451d154 return remains valid until a newly reviewed
delivery lands. No Lean file needs repair or compilation for this incident.
