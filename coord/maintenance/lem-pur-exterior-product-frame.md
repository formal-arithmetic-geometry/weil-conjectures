Maintenance diagnosis for lem-pur-exterior-product-frame, NR stage 2
2026-10-18

The immediate repeated blocker was a broken transitive dependency, not a
provider empty answer. The NOANSWER runs show supervisor SIGTERM at the
2700-second worker deadline; codex-retry.json records no provider error.
The 14:56 worker and the resumed 18:26 worker both returned concrete server
compile failures. The latter's failure was reproduced independently using
tools/lean_file.sh against current server sources.

The required import chain includes PurityConventions -> PurityFiniteKummerLevel
-> IntrinsicCoefficientTwists -> DerivedPullbackTensorHom ->
CoefDerivedSystemEvaluationCalculus -> CoefficientRingedSequenceSite.
CoefficientRingedSequenceSite failed beginning at line 151 with successor
universe metavariables that could not unify with max u (t+1), followed by
missing declarations and the 100-error limit.

Instance tracing identified the high-priority
CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall. Its
coefficient category and small-site hypotheses use a successor universe.
The existing SheafOfModules.hasSheafify_coefficientUniverse and
wEqualsLocallyBijective_coefficientUniverse support the actual independent
coefficient universe. Selecting those removes the inference failure without
changing any mathematical declaration.

A concurrent maintenance repair landed as commit
66a202455b2663b759f3938417d6abbafba3f41c, in
lean/Sheaf/Paper/CoefficientRingedSequenceSite.lean. It disables the conflicting
generic instance in that module. This maintenance session independently
validated a local-priority variant, then detected the concurrent source
change before writing and preserved the already committed repair.

Current authoritative validation, each through tools/lean_file.sh with the
unchanged 60-second per-file limit, nice 19 and two threads:
- CoefficientRingedSequenceSite.lean: PASS, 7.2 seconds.
- DerivedPullbackTensorHom.lean: PASS, 50.2 seconds.

The item's mathematical work and node records were not changed. An experiment
omitting PurityConventions and SupportedHomPullback was reverted: stage 2
requires stated statement and proof dependency imports. Preserve both imports.
The sandbox main module is byte-for-byte equal to its pre-maintenance source;
.bak copies preserve the transient experiment. The sandbox report contains
this diagnosis and is the handoff to the next worker.

Next worker: retain all three saved packet modules and node records. Refresh
current sources and run deliver2.py NR lem-pur-exterior-product-frame --no-push.
The former shared dependency failure is fixed. Earlier runs also contained
independent kernel timeouts in the item's exteriorFrameTarget and theorem;
a main-module timeout after the dependencies pass must be diagnosed from the
new result, not confused with the now-fixed universe failure. No item delivery
or complete packet validation is asserted by these dependency checks.

Full local evidence is under
/home/ubuntu/weil-launcher-all/maint/NR-lem-pur-exterior-product-frame-1792319160/evidence/.
No protected launcher, review or landing tool was edited, no concurrency rule
was added, and no global build or process termination was performed.

Final complete-packet validation, 2026-10-18 10:56 UTC:
The no-push delivery check returned exit 1. A repeated library check of
SupportedCupFunctoriality initially timed out. Current-source confirmation
compiled that module in 59.0 seconds, then timed out at 60 seconds in
PurityExteriorProductFrame. The shared universe failure did not recur.
A private local-reducibility diagnostic also timed out and was not applied.
The item remains undelivered; the remaining work is its main-module kernel
performance repair. Preserve the mathematical signatures and required imports.
See evidence/final-packet-dry-run.log and evidence/main-local-reducibility-compile.log
in the maintenance workspace for the completed checks.
