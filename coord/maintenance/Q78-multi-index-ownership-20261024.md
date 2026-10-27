# Q78 coordinate derivative ownership repair — 2026-10-24

The return of 07fdadb874c0 correctly requires the compact-submersion estimate to
cite a definition node for EuclideanSpace.multiIndexPartialDeriv rather than the
unrelated Fourier theorem. The worker implemented that extraction, but the
stage-2 packet reader excludes the former owner node outside the estimate's
prerequisite closure and then rejects its changed module as unowned. Repeating
the same packet cannot repair this classification mismatch.

This maintenance change extracts the already reviewed concrete definition into
Sheaf.Analysis.MultiIndexPartialDeriv and registers its definition node. The old
Fourier module publicly imports it; the definition's signature and body and the
Fourier theorem's signature, docstring and proof are preserved. The Fourier node
now cites the definition in stmt_deps and stops claiming its moved declaration.
The new node's review records this mechanical extraction, not a new mathematical
proof or the independent review of the estimate delivery.

The two modules are landed together using tools/land_set.sh, which invokes
tools/lean_file.sh sequentially with the configured 60-second per-file limit.
Existing files have adjacent .maint-Q78-owner-20261024.bak copies. The landing's
own backup and request retain the source transaction for ordinary build review.
No full build is started by maintenance.

The item worker should fetch current sheaf-dag and retain the repaired estimate,
its real definition dependency, and its report. Matching definition/Fourier
files in the sandbox contribute no delta after rebasing. Run the normal
batch2/deliver2.py Q78 lem-sfb-compact-submersion-phase-estimate --no-push, then
continue normal delivery and independent review. Keep the existing return until
the repaired item is accepted. Never cite the Fourier theorem as a false premise.

No dispatcher, admission, review, preflight, or landing tool is changed. A general
solution for future owner migrations needs the protected delivery reader to
classify an explicitly authorized former owner consistently with module
ownership; this maintenance resolves the present shared-module data first.
