Maintenance for K4 / Sheaf.Paper.DiagonalDncAffineModel, 2026-10-27

The repeated delivery failure was a stale client compile result. The private
overlay had compiled SfP1ChartExchange from commit
360cd023feb858778e000872ea3becb49fe0a920 with three unused-simp warnings. The
delivery tool rejected those warnings although the four requested modules
compiled. Server commit 6230b2a04268b44384fe7300280e482fcd407b66 removed the three
arguments, but lcompile._dep identified only the publication and sandbox
artifacts. A committed dependency repair therefore left its six-hour cache key
unchanged. The old warning output was replayed after the source repair.

The installed launcher patch includes git HEAD:lean in the dependency key.
Source repairs invalidate stored results before the next green publication;
metadata-only commits preserve reuse. When the source tree cannot be read, a
unique identity avoids reusing an unverifiable stored result. Existing
publication and sandbox artifact checks remain part of the key.

Active file on the launcher machine: /home/ubuntu/weil-launcher/lcompile.py.
Backup: lcompile.py.bak-maint-K4-DiagonalDncAffineModel-1793031476 beside it.
This directory contains the tested source, baseline .bak, patch and regression.
compile_attach.py is an unchanged supporting copy so the test also runs here.

The integrity guard initially restored the edit. The documented command
`python3 /home/ubuntu/weil-launcher-all/integrity/check.py --accept
/home/ubuntu/weil-launcher/lcompile.py` registered exactly this maintained file.
The guard manifest and pristine baseline were backed up with the same suffix.
guard-registration.txt verifies that only the compiler's manifest entry changed.

Validation:

- The regression fails on the old compiler by returning the old warnings after a
  real source-only git commit. All three tests pass on the repaired compiler:
  source repair refreshes a stored result, metadata commits retain it, and an
  unavailable source snapshot prevents reuse.
- Run from this directory: `python3 test_source_cache.py lcompile.py`.
- On the project server, compiled only SfP1ChartExchange with tools/lean_file.sh,
  SHEAF_FILE_TIMEOUT=60 and SHEAF_FILE_RUN_LIMIT=300. Exit 0, no diagnostics,
  `Compiled in 25.3 s` (SfP1ChartExchange-compile.log).

The worker sandbox retains its own mathematics and records. The assigned theorem
has no remaining hole and the worker's two split-off geometric lemmas each have
one hole. Resume normal lcompile.py / deliver3.py commands from a new process.
An already running compiler keeps its existing request; let it return. Do not
restore archived dependency warnings, change the item's statement or plan, or
remove the warning gate to address this tool failure. Publication and landing
remain the normal pipeline's work.
