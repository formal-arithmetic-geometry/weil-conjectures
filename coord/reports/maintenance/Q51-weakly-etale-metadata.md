# Q51 weakly-etale metadata maintenance — 2026-10-16

The delivery at b2e7fe8e6e was returned for missing chapter/unit metadata and
unbundled citation/search evidence. Subsequent workers repaired their evidence
and prepared source-faithful metadata, but deliver.py:204 could only update the
realization of an existing authoritative unit. The new main-20261015 chapter and
unit did not exist. tools/units.py still read and stamped only the master
snapshot, and sync_newtargets.py could reintroduce null live-import bindings.

The generator now accepts --snapshot and repeatable --unit selections, reads
companion proof files, recognizes either snapshot in node source paths, and
backs up changed files. Existing realizations are kept. The live sync fills
missing source-based bindings from installed records; explicit live bindings
still win. No Lean, proof, statement, chapter route, or unit route was changed.

Applied under coord/.merge.lock:

    python3 tools/units.py build --snapshot main-20261015 \
      --unit sk-lem-pe-weakly-etale-stability --unit sk-def-pe-morphisms

This installs the chapter and two exact-source units, with empty realizations,
and stamps the item, sk-def-pe-morphisms, and its comparison detail. The worker
owns the item's realization and must submit it with the ordinary delivery.
Eighteen regression checks pass, including preservation of existing bindings,
targeted scope, companion proofs, and replay of null/explicit live bindings.
The worker's existing proof and evidence are retained. Normal delivery/preflight
must still validate the repaired packet and reachability of the cited definition
unit. Final validation and commit IDs are recorded in the maintenance REPORT.md
on the launcher machine.

Backups: *.maint-Q51-weakly-etale-1792156931.bak for tool/report files,
*.units-<nanoseconds>.bak for generated records and stamped nodes. An empty
backup marks a newly created file.

The generator also writes ROOT/dag/nodes directly rather than following the
SHEAF_DAG read overlay. The first run exposed that inherited hazard and stamped
three live-project working-tree records instead of the side-project records.
Those three metadata-only edits were immediately restored from exact backups
under the live merge lock; each restored file was verified byte-for-byte equal
to live HEAD. The corrected run stamps only this side project, and a regression
test makes the external read overlay different and verifies it stays untouched.

Final packet validation: the unchanged delivery packager and repository preflight
passed in a private frozen checkout of a701a0d453d1170d61453f0c11d338e77f0c150f:

    OK (not pushed) deliver/Q51/sk-lem-pe-weakly-etale-stability at 1b7ef1cbda: preflight passed

Worktree acquisition and fetch alone were supplied by the private frozen checkout;
the real deliver.py packaging, citation/search checks and repository preflight ran
unchanged. The first post-metadata preflight reported one unit-reachability issue:
the sandbox had dropped the source definition citation sk-def-pe-morphisms while
that definition was still imported. It is now independently reviewed. Maintenance
restored its citation and statement dependency, retaining both precise older
definitions and all five proof steps and evidence unchanged. The exact reference
patch is archived beside this note as Q51-weakly-etale-reference.patch and is
already applied in the worker sandbox. The report's obsolete metadata-blocker
sentence was updated. Packet/report backups are adjacent in that sandbox.

The same exact-source metadata and generator were installed at the live import in
ec7bf11235d1111c6251da362c3e786ccdb12d38, under its own merge lock. That also
protects the side repair while the existing old sync process remains running;
no other process was stopped. All 18 regression checks pass in both repositories.
No Lean source or mathematical proof was changed, and maintenance pushed no item
delivery. Some interactive normal delivery calls were interrupted by signals
before reporting a result. A detached ordinary no-push run is separately recorded
in the launcher's evidence/normal-delivery-result.json. The final REPORT.md there
states its actual outcome. The current worker should rerun the ordinary delivery
and continue the established worker/second-reader flow; the missing-record and
definition-reference defects themselves are repaired.

Ordinary execution also passed: the exact normal deliver.py Q51 command with
--no-push and the default shared pool completed with exit code 0 at
2026-10-16T13:54:03.996873+00:00 (started 13:40:54 UTC):

    OK (not pushed) deliver/Q51/sk-lem-pe-weakly-etale-stability at d763c10294: preflight passed

This is the actual ordinary detached execution, distinct from the isolated
replay at 1b7ef1cbda. The result JSON is archived as
Q51-weakly-etale-normal-validation.json. The repaired packet passes the ordinary
pipeline, including citation/search checks, maintainer metadata preservation,
unit realization/reachability, review_split.py and DAG-delta preflight. No item
delivery was pushed by maintenance. The live-to-side periodic sync was also
observed after live metadata commit ec7bf11235; all repaired bindings survived.
