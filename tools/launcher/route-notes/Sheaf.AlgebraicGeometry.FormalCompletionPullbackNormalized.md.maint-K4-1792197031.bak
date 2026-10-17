Maintenance 2026-10-17: the ten NOANSWER attempts were Codex provider HTTP 429
failures, not mathematical failures. All ten attempts from 1792195909 through
1792196711 ended with `429 Too Many Requests` and wrote no last.txt.

The reviewed saved delivery 3cbddb91b3 landed at c070278e531893762fc3a8ec1d372e681ae2d172
(landing 20261017T003424-L-3316109). Its claim and return were closed normally.
The item compiled on the server with tools/lean_file.sh, timeout 60 seconds,
in 2.8 seconds. This is a single-file check, not a global-build certification.

If assigned again, compare current main with the preserved sandbox first. The
post-sync helper owner is WeilConjectures.AlgebraicGeometry.FormalSystemsPullback;
the proof needs `import all` of that module. The Sheaf wrapper cannot expose its
private helpers. Preserve the statement and use the already written proof.
Continue normal dry-run and independent-reader checks if a new delivery is needed.

The shared Codex runner now resumes temporary 429 failures within the original
worker budget and retains the sandbox. Exhaustion reports a provider BLOCKED
diagnostic. Do not replace a real theorem proof, reset failure counts, or restart
the argument merely because a provider call failed. Check any interrupted delivery
process's result before repeating it.
