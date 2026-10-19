# Maintenance: independent-universe derived Hom global sections

The stage-2 retries of `lem-coef-derived-system-evaluation-calculus` were caused
by an unusable recorded interface of `lem-pur-rhom-global-sections`, not a
compiler, SSH or permission failure. Its recorded theorem required the site
objects, site arrows, coefficient rings and module sections all in one universe.
The actual pro-etale site of `Y : Scheme.{t}` has objects in `t+1`, arrows in
`t`, and completed coefficient sections in `max (t+1) u`. Even `u=t` cannot
make those types match. A fresh server `tools/lean_file.sh` reproduction of
the retained `RhomDependencyProbe.lean` rejected the coefficient argument in
1.6 seconds, exactly as the workers' local and server confirmations did.

The bottom-up instruction at the end of the worker prompt forbids stating
another DAG node in the item's delivery. The worker therefore repeatedly
reported this prerequisite. Failure counts are historical and remain untouched;
retrying the same incompatible interface cannot fix it.

An earlier maintenance commit `33198b9a19c5f79a1dbdc66987930c0e0308aac6`
already repaired the analogous tower-limit interface. The current regression
probe verifies that interface too. The NQ delivery in `coord/deliveries.log`
at 04:21:02 UTC is the stage-1 split (`e1c311fa4d`), not an existing stage-2
statement. No item-specific stage-2 rejection appears in the current NZ returns.

## Repair

- Added `lean/Sheaf/Algebra/Homology/RingedSiteZerothHypercohomologyOfUniverses.lean`.
  Its real definition `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`
  is the right derived functor of `Hom_R(R,-)` followed by zeroth homology,
  using the already recorded independent-universe Grothendieck infrastructure.
- Added `lean/Sheaf/Algebra/Homology/RhomGlobalSectionsOfUniverses.lean`.
  `CategoryTheory.rhom_global_sectionsOfUniverses` gives the same natural
  additive equivalences and pre/postcomposition formula, using the recorded
  `derivedInternalHomOfUniverses` and the generalized hypercohomology definition.
  It is a stage-2 statement with one `sorry` and a complete proof plan, checked
  against local Stacks `sites-cohomology.tex`, Lemma 08JA and its proof.
- Changed only `lean` in the existing records
  `dag/nodes/sec-smooth-purity/def-pur-ringed-site-zeroth-hypercohomology.json`
  and `dag/nodes/sec-smooth-purity/lem-pur-rhom-global-sections.json`.
  The signatures are copied verbatim from the new sources. The mathematical
  statements, graph edges, proofs and historical reviews are unchanged.
  The note explicitly identifies the V4 proof as applying to the legacy theorem;
  the generalized theorem is not claimed proved.

Both companion modules publicly import their legacy modules. Existing callers
retain their original APIs and proved theorem. The new companion names are
necessary: the side compiler intentionally uses the published live artifact
for any module also present in the live project. Editing the side copy of the
legacy module alone would leave ordinary worker imports using the old API.
No live source or published artifact was changed.

The new interfaces keep site object and morphism universes independent, with
coefficients and modules in `max c v r`. Sheafification and locally-bijective
instances are the canonical infrastructure already provided for the actual
completed coefficients. No universe equality, alternate site, arbitrary
comparison, coefficient flatness, boundedness or product-exactness is assumed.

Backups of the two changed records and initial copies of each new module are
the corresponding paths with `.maint-NZ-1792135887.bak` appended. This new
report has the same backup suffix. No process was stopped. No Lake build ran.

## Validation and handoff

All validation used `tools/lean_file.sh`, which enforces nice 19, two threads
and 60 seconds per Lean file. After the final source changes, the imported
hypercohomology companion compiled in 1.4 seconds, the Hom comparison in
1.9 seconds, and the actual-site regression probe in 2.3 seconds, with no
warnings or errors. Imports were compiled one file at a time into the private
overlay. The probe is retained at
`lean/.sandbox/maintenance-NZ-1792135887/RhomIndependentUniverseProbe.lean`.
It also checks both legacy declarations and the generalized tower limit.

The next item worker should read the refreshed dependency records and import
`Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`. On the actual pro-etale
site, use:

```lean
attribute [local instance] HasDerivedCategory.standard
#check rhom_global_sectionsOfUniverses.{t + 1, t, u}
  (AlgebraicGeometry.Scheme.ProEt.topology Y)
  (completedIntegralCommRingSheafUnrestricted l E Y)
```

For explicit operations use
`ringedSiteZerothHypercohomologyOfUniverses.{t + 1, t, u}` and
`derivedInternalHomOfUniverses.{t + 1, t, u}` at these same arguments.
The fourth universe parameter is the chosen derived-category localization.
The default standard instance in the probe is only localization infrastructure.
The original failing probe intentionally names the legacy theorem and should
continue to fail at this site; use the new recorded declaration.

The item's statement, mathematics and delivery remain the stage-2 worker's
job. Do not restate these dependencies in its sandbox. The old normalization
concern in historical reports was not a confirmed compiler failure.
