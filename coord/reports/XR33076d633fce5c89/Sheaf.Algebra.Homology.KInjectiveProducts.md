## What changed

Restored the three original public Mathlib imports in
`lean/Sheaf/Algebra/Homology/KInjectiveProducts.lean`, undoing the import removal
from landing 20261014T090919-L-366279. This restores the public environment on
which the global build's generated axiom/sorry consumer relies.
Change record: `coord/changes/KInjectiveProducts-retired-imports.md`.
No other source, node or configuration is changed. Existing docstrings are
preserved verbatim as requested; their historical claim of no remaining imports
is superseded by this repair record.

Validation used only the local single-file `lcompile.py` command with its
unchanged 60-second limit and remote fallback disabled:

- Restored module: exit 0, 1.1 seconds, no warnings or errors.
- Same allowed file with the exact stage3 declaration probe temporarily
  appended: exit 0, 1.3 seconds, `SHEAF-PROBED 0`; no axiom/sorry findings.
  Its only warning was the auditor's existing line exceeding 100 characters.
  The probe was removed immediately after this diagnostic compilation.

No delivery command, global build, server compile, push, second-reading evidence
or `.check` file was created. The delivery dry run writes in the read-only
snapshot, so it was not run under this repair's stricter sandbox restriction.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0.
The module has no declarations and no sorries. The previously retired
`CochainComplex.termwise_product_isKInjective_and_isLimit` remains absent.
No target statements, proofs, definitions or axiom rules change.

## No longer needed

No imports are pruned in this repair. The previous removal of
`Mathlib.Algebra.Homology.HomologicalComplexLimits`,
`Mathlib.Algebra.Homology.DerivedCategory.Basic` and
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective` is reversed.
No modules or nodes are retired or added, and no consumer source adaptation
is necessary.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery treated zero source importers and a successful standalone
compile as sufficient evidence for removing every public import. The generated
global-build BatchProbe is also a consumer: its `open Lean Elab Command` and
`run_cmd` require the original transitive elaboration environment. The recorded
global failure confirms that the import-free module broke this consumer even
though the empty source itself compiled. Restoring the pre-landing imports
repairs the interface instead of changing or bypassing the audit.

## Second reading by XR33076d633fce5c89

Independent review of request.json, delivery.diff, both scoped repair files,
the first reader's report, and the repository's stage-3 brief, standards and
review points. Verdict: PASS; the recorded red-build failures are repaired.

1. Interface and mathematics: compared the repair with the snapshot and the
   failed landing diff. The three public imports exactly restore the interface
   from before that landing. There are no declarations in this compatibility
   module, so no signature, hypothesis, conclusion, definition or target changes.
   The historical import-free docstring remains unchanged from the failed
   landing; this repair record and report explicitly supersede that claim.
2. Compilation and trust: independently compiled the delivered Lean file using
   only lcompile.py, with remote fallback disabled and its unchanged 60-second
   per-file limit: exit 0, 1.1 seconds, no warnings or errors. Also created fresh
   temporary module/consumer pairs and compiled each pair in dependency order
   using lcompile.py. The import-free counterfactual compiled in 0.2 seconds but
   the exact tools/build.py BATCH_PROBE consumer failed in 0.2 seconds with both
   recorded errors: unknown namespace Command and missing Lean.Elab.Command.
   The repaired module compiled in 1.1 seconds and the same consumer compiled
   in 1.6 seconds, reporting SHEAF-PROBED Sheaf.Algebra.Homology.KInjectiveProducts
   0, with no SHEAF-AXIOM or SHEAF-SORRY findings. Its sole warning is the unchanged
   auditor's long line. The delivered source adds no axiom, sorry, unsafe,
   opaque, implemented_by or extern workaround. There is no local declaration
   for which a separate #print axioms command is applicable.
3. Split statements: none added or retained in this declaration-free module;
   no new nodes, hollow definitions or witness choices. Holes closed 0, added 0.
4. Route and pruning: the retired duplicate remains absent. No proof-dependency
   or unit route changes; no imports are pruned by this repair. Public visibility
   is necessary to restore the generated consumer's environment. Source import
   search found no direct Lean importers requiring adaptation. The earlier
   standalone compilation missed this generated consumer; the counterfactual
   above verifies the reported cause rather than bypassing the audit.
5. DAG consistency: read lem-pc-ringed-space-product-kinjective and its unit
   sk-thm-picard-duality. The node already records retirement with lean: null and
   the caller specializations. This import-only repair neither restores the
   duplicate nor changes the node statement, proof, dependencies, origin or
   unit realization. No DAG edits are needed.

Second reading changed only this report section and wrote .check; the repaired
Lean file and change record were accepted as written. Temporary diagnostic
sources were removed. Normal delivery uses local single-file compilation only;
server compilation is disabled.
