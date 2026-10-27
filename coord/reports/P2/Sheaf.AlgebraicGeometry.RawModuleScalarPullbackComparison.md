## What changed

Fresh resubmission compile (2026-10-23 15:30 UTC): lcompile.py --all
completed for all fourteen modules with exit code 0 and no Lean diagnostics.
The delivery invocation sets LCOMPILE_NO_LOCAL=1 so its required compile and
axiom probes use the project server backend before fresh-base preflight and push.

Fresh resubmission audit for C-d6228 (2026-10-23): the retained reviewed
construction repair is reconciled with current shared source. The audit covers
24,726 live and quarantined modules and 346 matching consumers. The newly
matched Sheaf.Paper.RootTowerFiniteTensor uses CategoryTheory.forget, so its
statements and source need no adaptation; its row is now in
coord/changes/P2-retire-raw-module-scalar-pullback-comparison.md. No consumer
row remains missing. The twelve node copies change only permitted fields,
every proof_deps list agrees with its proof steps, and the withdrawn
source-square node has no incoming dependency or unit realization. All
fourteen retained Lean modules have zero holes; all thirteen adaptations are
unclaimed. The required rebuild on fetched sheaf-dag is performed by
deliver3.py, without changing the read-only checkout manually. The affected
record remains present at coord/changes/P2-derived-pullback-reuse.md.

The fresh server preflight found one newly present consumer missing from the
Users table: Sheaf.Paper.ParameterRootIntegralNilFibre. Its actual occurrences
are Scheme.ProEt.forget specZ and categorical scheme pullbacks in the
profinite-test collapse and closed-fibre constructions. It is unclaimed and
requires no source edit. The main change record now includes this explicit
consumer check. That preflight stopped before pushing; the corrected packet
is submitted again through deliver3.py.

Current repair verification (2026-10-23 14:44 UTC): all fourteen retained Lean
modules compiled together through the required lcompile.py server backend with
exit code 0 and no Lean diagnostics. The interface audit of 24,605 live and
quarantined modules found 344 matching consumers, no missing Users rows and no
remaining imports of the withdrawn concrete source-square module. All fourteen
delivered modules still have zero holes; all thirteen adapted modules are
currently unclaimed. The twelve node copies change only permitted fields,
and each proof_deps list agrees with the union of the proof steps' uses.
The overlaid DAG has no remaining incoming dependency on the withdrawn node;
no unit realizes it. The reviewed construction repair is retained intact.
The returned bare-basename failure is addressed by including and identifying
the change record at coord/changes/P2-derived-pullback-reuse.md. deliver3.py
performs the required fresh-base rebuild and preflight before pushing.

Resubmit reviewer-approved head d62288e2e4c after the C-d6228 return.
The reported landing failure was --apply-fixes naming
P2-derived-pullback-reuse.md without its repository directory. The retained
packet includes coord/changes/P2-derived-pullback-reuse.md; its resubmission
note now names this return and its full delivery path. All five change records
remain open. The retained Lean repair is compared with current shared source,
and deliver3.py rebuilds the single delivery commit on freshly fetched sheaf-dag.
No reviewed mathematical change is discarded or replaced by a rebase alone.
The latest return again reports the bare-basename landing error. The affected
record now explicitly instructs the landing reader to address any correction at
`coord/changes/P2-derived-pullback-reuse.md` relative to the delivery root.
This refresh compared the retained Lean repair and all twelve node copies with
current source, verified the permitted node fields and proof-step dependencies,
and compiled all fourteen modules through lcompile.py with exit code 0 and no
diagnostics. The current full interface audit covers 24,567 live and quarantined
modules and 344 matching consumers. Three new textual matches are recorded in
the main change record: EllAdicLocalizingBrownRepresentability uses
CategoryTheory.forget; ParameterRootBoundaryData uses categorical pullback;
QcqsConstructibleIntegralLatticeTree, held by A7, uses categorical pullback and
Mod.forget. No source adaptation is needed. The migrated import graph has no
remaining importer of the one withdrawn module. The older audit counts below
record prior snapshots.
The refreshed interface audit finds one additional name match in
Sheaf.Paper.RelativeProductCoefficientFactorSquares. Its pullback denotes the
categorical fibre product, not RawModuleScalarComparison.pullback; the main
change record now documents this consumer check. No source adaptation is needed.
After the interrupted provider call, the retained delivery log and process list
were checked before resubmission: no delivery was still running. A fresh server
compile of all fourteen modules completed with exit code 0 and no diagnostics.
The refreshed complete interface audit covers 24,395 live or quarantined modules
and 341 matching consumers, with no missing consumer rows and no remaining
imports of the withdrawn module. All twelve node copies again pass the
owned-field and proof-dependency consistency checks.

Repair the returned c4917322e6a packet and reconcile it with the current library.
The return required the original H9 consumer compiler error, exact forced
import change and H9 holder attribution. Those checks and records were supplied.
The 2026-10-23 09:01 UTC quarantine then moved H9's consumer
Sheaf.Paper.CartierRelativeBoundaryRealization and four prerequisites out of
lean/. Restoring that consumer would require unrelated rework. The final packet
therefore preserves its archived source verbatim and keeps this item's import
path as a small compatibility module. It publicly imports
RawModuleScalarDerivedPullbackIso, with no declarations or duplicate data.

The adopted upstream twin supplies pullbackIso, pullback, freeAbelian and
freeMap. RawModuleScalarDerivedPullbackIso retains forget and its three instances
as aliases to moduleAbelianForget and its proved instances. The item reexports
this complete API, including for its quarantined parent. It is no longer in
deleted.txt. The H9 source file is not in this delivery; its quarantine archive,
Lean attachment and dependencies are untouched. No adopted source file changes.

The thirteen adapted live modules retain the prior canonical-construction repair:
RawModuleAbelianHomMap, RawModuleScalarSourceFactors and
RawModuleScalarSourcePrefix reexport their proved upstream twins;
RawModuleFreeSourceHomBijective and RawModuleScalarSheafComposition prove the
scalar-unit equations from the adjunction mate; RawModuleScalarClassMorphisms
and ComparisonForgetScalars use the compatibility API; RawModuleFreeSourceAcyclic
migrates its import. RawModuleScalarSourceClassFormula, the unshifted coefficient
result and the shifted coefficient square reuse complete canonical proofs.

The derived comparison is the inverse canonical forward comparison. The private
reverseDerivedComparison and public derivedPullbackIsoImpl_eq_formula identify
it with the original three-factor reverse composite. The historical
derivedPullbackIso name reuses this construction.

OrdinaryFiniteP1Kummer constructs its scalar root generator as the scalar-extension
adjunction transpose of the sheafification unit, using Mathlib's direct
HomEquiv.toRestrictScalars component. This is definitionally the old forgotten-unit
composite. A proved private adjunction lemma supplies naturality. Integral
generator and Ext-class realization data are preserved. Local transparency
settings protect scalar extension and the concrete derived localization.

Only RawModuleScalarSourceSquare is withdrawn. Its unused concrete theorem is
replaced in the actual coefficient and source-class proofs by the generic core,
which the canonical library already proves. Four stale statement dependencies
are corrected to the derived-comparison construction node. Their equations,
hypotheses and comparisons are unchanged; the statement_change records include
the citer audit. The unused node remains with lean null. No unit realizes it,
no proof step uses it, and live/quarantined source scans find no consumer.

All five retained change records list actual consumers, including the consumers
named in previous returns and those added during this repair. A scratch audit
now derives its interface names from every actual source diff and searches both
the old and migrated import graphs, including quarantine. It reports missing
rows and remaining imports instead of assuming the original consumer set.
The final compile retry exposed expensive concrete derived localization
checking in OrdinaryFiniteP1Kummer. A profiler run took 49.7 seconds, with
41.7 seconds cumulative kernel checking. ordinaryFiniteClass now specializes
the public generic data constructor ordinaryFiniteClassCore, which evaluates
exactly its previous Ext composition with abstract instances. Unfolding the
helper recovers the old body definitionally; existing signatures, irreducibility
and data are preserved, and no consumer needs an adaptation. The profiled full
file then compiled in 26.4 seconds, with 22.9 seconds cumulative kernel checking.
This is implementation factoring within the same module and construction node,
not a file split or additional proof obligation. No compile limit changes.
No launcher or project tool is changed.

Change records:
coord/changes/P2-retire-raw-module-scalar-pullback-comparison.md,
coord/changes/P2-raw-derived-construction-reexports.md,
coord/changes/P2-derived-pullback-reuse.md,
coord/changes/P2-root-generator-adjunction-transpose.md, and
coord/changes/P2-prune-unused-concrete-source-square.md.

## Proved and sorry left

The assigned definition repair starts with zero holes and has zero holes.
Holes closed: 0 of 0. Holes added: 0. Split off: 0. Sorries left: none in any
of the fourteen delivered Lean modules, including the item compatibility module
and thirteen adapted live modules. The quarantined theorem
WeilConjectures.PurityFiniteSetting.cartier_relative_boundary_realization retains
its existing hole in its untouched archive; it is not delivered or restored.
This is a construction repair and duplicate retirement, not a proof-count gain.

The compatibility instances forward to proved upstream instances. The private
scalar-unit equations, generic adjunction naturality and derived inverse-comparison
equalities have complete proofs. The reexported canonical declarations already
have complete adopted upstream proofs.

Compiled scratch regressions reconstruct the original Kan/sheafification map,
prove its unit equation and identify it with the canonical map by injectivity
of the adjunction Hom equivalence. freeMap equality is checked by rfl. The
scalar-unit, naturality and derived inverse-comparison equations compile without
holes. They cover zero rings, zero objects, identity arrows and empty schemes,
without new hypotheses. Scratch files are not delivered.

Earlier fourteen-module packets compiled together through lcompile.py, including
the isolated original/adapted H9 checks below. Later delivery attempts also
compiled the whole packet but stopped before pushing: the first preflight found
RelativeKummerStrictLocalInvariance missing from Users; the next found
FramedForgetSupport, FramedScalarMaps, FramedTransport and
UnitKummerTwoSiteNormalization; their actual uses are now individually recorded.
The following attempt stopped on the newly quarantined H9 prerequisite imports.
The compatibility-module reconciliation addresses that failure without restoring
unrelated quarantined modules. Final deliver3.py reruns compilation, axiom probes
and preflight against freshly fetched main. A probe receiving no server answer
is recorded by that tool for the maintainer's merge check; no limit is raised.

## Forced adaptations

There is no source adaptation of another group's module in the final packet.
The current thirteen live adaptations are unclaimed. The H9 consumer was moved
to quarantine and is not restored. Its unchanged original import now loads the
same compatibility API through the item's retained import path. This removes
the need to adapt that consumer while preserving all its declarations and data.
The evidence requested by the original return is retained below as the check
of the superseded empty-item-withdrawal packet, not as a claim that the final
packet changes H9's archived file.


Sheaf.Paper.CartierRelativeBoundaryRealization is held by H9, as recorded in
coord/claims/Sheaf.Paper.CartierRelativeBoundaryRealization.lock. The original
shared-source file was compiled with lcompile.py against this packet's changed
dependencies in an isolated scratch sandbox. Both modules in deleted.txt were
compiled there as empty `module` files, matching their landed withdrawal form;
the published copies of their removed declarations were not used.

The original consumer fails (exit code 1), with the first error:

```text
lean/Sheaf/Paper/CartierRelativeBoundaryRealization.lean:112:4:
error(lean.unknownIdentifier): Unknown identifier `RawModuleScalarComparison.forget`
```

The missing abbreviation prevents cartierUnderlyingResolution from being
declared, producing further unknown-identifier errors at lines 226, 229 and 230.
The theorem's uses of the same abbreviation also fail at lines 221, 227, 231,
244--245 and 252--253, ending with:

```text
lean/Sheaf/Paper/CartierRelativeBoundaryRealization.lean:212:8:
error: (kernel) unknown constant 'AlgebraicGeometry.Etale.RawModuleScalarComparison.forget'
```

The entire source diff is line 12:

```diff
-public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison
+public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
```

This line is forced because the original import points to the item withdrawn
by this delivery. The replacement publicly exposes the retained forget
abbreviation and its instances, now supplied by the existing derived-comparison
module as compatibility aliases of moduleAbelianForget. Public visibility is
retained because cartierUnderlyingResolution and the theorem's signature use
that API. The one-line replacement restores those names without changing any
existing declaration, signature, visibility, data or proof in H9's module. Its
existing theorem hole is preserved and no hole is added. The adapted file
compiles with exit code 0 and no diagnostics in 20.1 seconds against the same
empty-withdrawal dependency setup as the original.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare. Its concrete
source-square theorem is unnecessary because the canonical source-class and
coefficient proofs use the generic core, and the shift proofs transport those
results. The four stale definition citations now point to the actual derived
comparison node. No DAG node is deleted and no unit route is bypassed.

The duplicate declarations formerly in RawModuleScalarPullbackComparison are
unnecessary; their canonical upstream implementations and historical forget API
are reexported. The module path itself remains necessary for the quarantined H9
parent and is retained. Its old Kan-extension construction and the two private
pullback_unit_hom expansions are removed. Public canonical APIs and their data
remain available.

The duplicate Hom-map, source-factor, source-prefix, source-class, coefficient
and shifted-square bodies are replaced by canonical theorem imports. The old
unshifted module's private Shift.ExactFunctor, RawModuleScalarSourceSquareCore
and RawModuleScalarSheafComposition imports are supplied by its canonical route.
The coefficient square uses canonical-square and compatibility imports. The
duplicate private congruence metaprogram is removed. No declaration or public
import is removed from lean/WeilConjectures; the constant-coefficient colimit
result remains used upstream.

## Where the brief, the DAG or earlier work was wrong

The latest C-d6228 return approved the packet and requested only a fresh-base
resubmission after a landing path error. It reported no additional proof or
definition defect. The affected change record is a new file relative to current
shared source, and the sandbox includes it at its complete repository path.
No launcher or project tool is changed to bypass the failed landing operation.
The refreshed change record gives the precise delivery-relative path required
for any reader correction. The sandbox contains that new file at that path.

During this repair, read-only Git status/log/tree inspection was mistakenly
used despite the brief's file-only inspection rule. It made no repository
mutation. Subsequent inspection uses source files, and deliver3.py performs
the authorized rebase, checks and push in its own worktree.

The generic brief describes a repeatedly split theorem. The current assignment
is the listed DIFFERENT upstream-twin retirement with zero holes. Its real
repair removes duplicate constructions while retaining the missing historical
forget names as aliases of the canonical exact coefficient functor.

The c4917322e6a return correctly identified the missing forced-adaptation report
and holder H9. Both were repaired with the actual original compiler failure,
exact one-line diff and matching adapted compile. The later quarantine changed
the current source: CartierRelativeBoundaryRealization and its four prerequisites
are absent from lean/ but preserved in quarantine by coord/rework.tsv. Their
absence does not authorize withdrawal or restoration without their rework.
Keeping the item's compatibility import path lets that parent be restored
unchanged. The archived source is preserved, and the superseded H9 adaptation
is kept only as scratch evidence. It is not in the packet.

The canonical pullback comparison is the unique unit-compatible mate, rather
than literally the original Kan/sheafification term. Equality of endpoints alone
would be insufficient; the compiled unit-equation regression identifies the
maps, and derivedPullbackIsoImpl_eq_formula identifies the derived composites.
The old concrete source-square attachment also named the derived comparison
instead of the unused theorem. Its four citers now refer to the actual
construction node, with their mathematical equations unchanged.

All twelve node copies were checked: only permitted Lean, proof and
statement-change fields differ from current source, and every proof_deps list
matches the proof steps' uses. Non-owned metadata is retained. No target
signature changes, no arbitrary witness is chosen and no hole is moved.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
