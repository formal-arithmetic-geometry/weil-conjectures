# Q13 stage-1 arXiv / Stacks-tag gate repair

Item: `lem-sfb-strict-codegree-polygon-gap@new`, stage 1.

The duplicate gate in `/home/ubuntu/weil-launcher-all/batch2/deliver.py`
matched `\b0[0-9A-Z]{3}\b` throughout serialized source metadata.
It interpreted the `0810` prefix of Morrison's `arXiv:0810.2340` as a
Stacks tag. Because the item has one non-elementary step citing its
finite-convex-minorant helper, the resulting false shared tag triggered
D1/D2. Writing additional non-duplicate comparisons could not clear this
unconditional rejection. Dispatcher state recorded 103 failures at the
start of this maintenance; retries continued during the investigation.

The deployed `dup_check` removes complete arXiv identifiers (YYMM.NNNN
or YYMM.NNNNN, with optional version) before scanning for Stacks tags.
A genuine `Tag 0810`, a Stacks tag URL, alphabetic tags, and real tags
alongside an arXiv reference still reach the unchanged duplicate gate.
The original source is preserved in `deliver.py.bak`; the deployed source
is `deliver.py`, with the exact change in `deliver.patch`.

The normal integrity record/save operations registered the authorized
runtime update under the guard's existing `.lock`. Adjacent backups with
suffix `.maint-Q13-source-tags-1792761041.bak` were kept for the runtime,
manifest and pristine source. No integrity guard code was changed.
No protected launcher file, review service or landing tool was edited.

Validation:

- The eight regression tests reproduced ten arXiv failures before the fix
  (including subcases), and all pass after it. Real Stacks collisions still fail.
- The five existing `test_stage1_request` tests pass.
- The unchanged sandbox passes duplicate, citation and logged-search checks.
- The real dry run completed with exit 0: server preflight passed at
  `26039f7e229`, and a durable stage-1 handoff receipt was saved.
- Runtime, integrity manifest and pristine source have identical hashes.

To rerun the gate regressions on this archived source:

```sh
STAGE1_DELIVERY_TOOL="$PWD/deliver.py" python3 -m unittest -v test_stage1_source_tags
```

This is a pipeline repair. No mathematical statement, proof, elementary
flag or citation was changed; no Lean file was edited or compiled.
The item was not pushed. Continue with the worker's required review /
handoff and delivery using the existing sandbox; the old BLOCKED note
about arXiv being a Stacks tag is obsolete. A successful maintenance dry
run is not a mathematical second reading.
