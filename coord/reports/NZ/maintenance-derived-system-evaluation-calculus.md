# Maintenance: derived system evaluation calculus

The repeated stage-2 failure of `lem-coef-derived-system-evaluation-calculus`
was caused by the published Lean interface of its already-stated dependency
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`. Its only recorded theorem used
`{C : Type u} [SmallCategory C]`, `RingCat.{u}` and
`ringedSiteModules.{u,u,u,u}`. The target requires the actual small pro-etale
site, with object universe `t+1`, morphism universe `t`, and coefficients and
module sections in `max u (t+1)`. This is a type mismatch, not a transient
compiler or SSH failure. Both local and server errors in the worker attempts
confirm it. The latest bottom-up brief prevented the worker from restating a
different DAG node, so repeated dispatch could not repair the prerequisite.

## Repair

- Added `lean/Sheaf/CategoryTheory/RingedStrictTowerHomotopyLimitOfUniverses.lean`,
  publicly importing the original module. Its theorem
  `CategoryTheory.ringedStrictTowerHomotopyLimitOfUniverses` separates the site
  object and morphism universes and uses coefficients/modules in `max uC vC r`.
  It retains all the old conclusions: the universal right-derived pair,
  computation on K-injectives, existence of tower resolutions, exactness,
  derived evaluation, natural Roos triangles, pro-zero vanishing and the cone
  criterion. Its source and full proof plan are attached to the existing DAG
  node. The proof remains `sorry`, as required for stage 2.
- Changed only `lean` in
  `dag/nodes/sec-proper-base-change/lem-weil-pbc-ringed-strict-tower-homotopy-limit.json`.
  The record points to the companion and quotes its signature verbatim. The
  mathematical node statement, proof and graph edges are untouched.
- The original module/declaration remains available unchanged. A distinct
  side-only companion is deliberate: `tools/nt_compile.py` and the launcher's
  overlay use published live artifacts for modules already present in live
  sources, while compiling side-only modules into a private overlay. Changing
  the side copy of the old module alone would not expose the new declaration
  to ordinary worker imports.

The server node backup is the same path followed by
`.maint-NZ-1792134467.bak`. The new module and this report also have `.bak`
snapshots. No global build or live source/artifact modification was used.

## Validation

The normal `scompile.py` wrapper compiled the companion locally, both as a
sandbox statement and under its actual module name, without errors or
warnings. Server `tools/lean_file.sh` compiled the companion in 1.9 seconds.
A separate probe importing the companion and `CompletedIntegralCoefficients`
compiled the imported companion in 1.8 seconds and the probe in 1.6 seconds.
Each invocation retained nice 19, two threads and the 60-second file limit.
The probe also checked that the legacy declaration remains visible.

The former failing application now type-checks with independent `t` and `u`:

```lean
attribute [local instance] HasDerivedCategory.standard
#check ringedStrictTowerHomotopyLimitOfUniverses
  (AlgebraicGeometry.Scheme.ProEt.topology Y)
  (completedIntegralCoefficientSheafUnrestricted l E Y)
  (completedIntegralCoefficient_mul_commUnrestricted l E Y)
```

The sheafification and locally-bijective typeclass binders are the canonical
abelian-category infrastructure already supplied by the completed-coefficient
module. Their universe includes the site. They impose no coefficient flatness,
exactness of countable products, or equality of site universes.

## Next worker

Read the refreshed dependency record and import its new companion module.
Use the generalized declaration above on the actual completed coefficient
sheaf; retain the original site and coefficient universes. The target's
mathematics and delivery remain the stage-2 worker's job. The earlier report's
normalization-interface concern was not a confirmed compiler failure; inspect
the current normalized-tower declaration when developing the target rather
than treating that old observation as another established blocker.

The dispatcher failure count is historical and was not reset. No worker was
stopped and the item remains eligible for dispatch.
