## Worker report

Current validation (2026-10-21): the prescribed deliver2.py --no-push passed
preflight and clean server compilation for the retained one-module packet,
printing OK for commit c48d8a5b51b. The failure history below is retained for
traceability and is superseded by this successful validation. No upstream patch
is part of this delivery.

This is an undelivered draft. The mandatory compiler wrapper failed before elaborating this
module on two attempts. It tried to compile overlay
WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism and failed at its import
with `unknown module prefix 'Mathlib'`; its server fallback then reported
`Live published library is unavailable`. No tools or live sources were modified. The resumed attempt ran the required dry run and direct compiler confirmation; both failed
before elaboration because the published library is unavailable. No push was attempted.

The draft module Sheaf.Paper.DiscreteExchangeSiteComparison states the exchange equality
and the boundedness/classicality of its two pro-etale endpoints. Its only theorem proof is
`sorry`, with all seven natural-language proof steps in its docstring. No new notion or
canonical comparison is defined.

Hypotheses and clauses:

- The discrete commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`. There is
  no topological structure, finiteness, torsion, characteristic or properness hypothesis.
- The schemes and four arrows are the explicit `Scheme.{u}` binders. The Cartesian square
  with chosen identification is `sq : ChosenCartesianSquare g' f' f g`.
- Quasi-compactness and quasi-separatedness are the four instances on f and f'. There are
  no such assumptions on either horizontal edge.
- The input L is in the module-valued small-etale `DerivedCategory.Plus`. This is the
  recorded six-functor coefficient encoding of the derived-category dependency.
- A_T is `(comparisonUpperStar (ModuleCat Λ) T).mapDerivedCategory`, restricted through
  the existing fully faithful `DerivedCategory.Plus.ι`.
- The canonical a is the existing `leftDerivedUpperStarComparisonIso`. The direct-image
  factor of b is `rightDerivedLowerStarComparisonPlusIso`, the derived base-change map
  of `lowerStarComparisonUpperStarBaseChange`. The recorded
  `directImageMateCompatibility` supplies precisely its counit normalization.
- S and T are the existing natural isomorphisms `baseChangeSourceComparisonIso` and
  `baseChangeTargetComparisonIso`. Their source definitions were read in full: they
  paste exactly the inverse-image and canonical direct-image factors displayed in the
  node, with the canonical D+-inclusion comparison isomorphisms. Their NatIso types
  encode both invertibility and naturality in L, without an arbitrary comparison choice.
- The first conjunct is `A_Y'(e) ≫ T = S ≫ e_p`, in Lean's left-to-right composition
  order. The etale map is the recorded `Etale.derivedBaseChangeMapPlus`; the pro-etale
  map is the existing constant-module specialization `ProEtale.derivedBaseChangeMap`.
  Its definition was read: it is literally `mateEquiv` of the specified canonical
  derived-pullback composition square under the derived edge adjunctions. This is the
  ordinary constant-ring ringed mate, not a completed or condensed coefficient exchange.
- The next two conjuncts assert a lower bound and `IsClassicalComplexFor` of
  `Lg* (Rf* (A_X L))`. The final two assert those properties for `Rf'* (Lg'* (A_X L))`.
  The objects are explicitly written out. The equality is stated in the ambient derived
  category through the faithful D+ inclusion; the bound clauses give membership in D+.
- `IsClassicalComplexFor` is the existing all-integer-cohomology continuity-map predicate
  from ClassicalDerivedDefinitions, publicly used by the comparison theorem's classically
  valued interface. No local classicality predicate is introduced.

Dependencies inspected and imported include ChosenCartesianSquare, Mathlib QuasiCompact
and QuasiSeparated, Scheme.proEtaleSiteComparison, Scheme.ProEt, constantSheaf,
ringedSiteModules, Etale's module derived categories, proEtaleConstantRingDerivedPullback,
ProEtale.directImageComparison, mateEquiv, Etale.derivedBaseChangeMapPlus, the ambient
ringed exchange module and ClassicalDefinition. The source ModuleCat realization and
endpoint isomorphisms are imported from
WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange. The classical predicate
is imported from Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions. Proof-dependency
modules are explicitly imported too, including exact descent, localization, cohomology
comparison and the classical sheaf essential-image theorem.

Source read: main-20261015 sk-thm-properbasechange.proof.md, particularly its pro-etale
paragraph; Stacks sites-cohomology.tex, remark-base-change (07A7). Also read the complete
item and the statements/Lean records of every statement dependency. No repair note for
this item was present.

Edge cases inspected mathematically: identity vertical/horizontal maps, zero input,
zero coefficient ring, arbitrary infinite rings such as Z, and the empty scheme. The
formulation imposes no Nontrivial, Nonempty, finite, proper or exchange-isomorphism
assumption. The ring lives in the established common larger coefficient/site universe.
Compilation has not yet confirmed elaboration of the draft.

Searches through the prescribed msearch.py wrapper:

- LeanFinder: `Canonical etale proetale comparison identifies derived base change exchange
  for an arbitrary discrete commutative ring` returned eight etale ring/base-change
  declarations (RingHom.Etale.isStableUnderBaseChange, RingHom.Etale.respectsIso,
  Algebra.Etale.comp, StandardEtalePair.homEquiv_apply_coe, Algebra.Etale.of_equiv,
  KaehlerDifferential.isBaseChange_of_formallyEtale, StandardEtalePresentation.mapEquiv,
  StandardEtalePair.homEquiv). None gives the target.
- Loogle: `"proetale", "baseChange"` returned only
  AlgebraicGeometry.Scheme.instIsStableUnderBaseChangeProetalePrecoverage.
- Mathlib grep: `(pro[Ee]tale|proetale).*(exchange|baseChange)|(exchange|baseChange).*(pro[Ee]tale|proetale)`
  returned zero hits.
- Project rg/grep for the item id and exchange/comparison names found the existing
  `comparison_derivedBaseChangeMap` and its S/T definitions. Its full signature allows
  arbitrary commutative rings, despite the FiniteCoefficient directory names. It gives
  the equality, but not this item's additional classicality and boundedness assertions.
  The recorded finite transport node itself does not state the full present node.

## Validation blocked

Both prescribed scompile.py attempts failed in the wrapper's overlay before checking the
new file, with the same missing Mathlib prefix and unavailable published-library message.
No clean-compile claim, independent second reading or delivery is recorded.


## Resumed validation, 2026-10-21

Retained the saved Lean module and node unchanged. Inspected this report, the complete
saved node and module, the recorded searches, and the required stage-2 instructions.
No item-specific repair note exists in the shared checkout.

First ran the prescribed `deliver2.py Q14
lem-weil-pbc-discrete-exchange-site-comparison --no-push`. It failed before checking the
new module while compiling the overlay
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism` at line 6:

```
object file '/home/ubuntu/weil-conjectures-sheaf/lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/AlgebraicGeometry/Morphisms/Constructors.olean'
of module Mathlib.AlgebraicGeometry.Morphisms.Constructors does not exist
```

The wrapper's server confirmation said `Live published library is unavailable`.
A subsequent direct prescribed `scompile.py Q14
lem-weil-pbc-discrete-exchange-site-comparison` invocation on the saved module returned
exit 1 with the identical missing object and server confirmation. Thus neither call
reached the draft's elaboration or produced a draft-specific diagnostic to repair.
This is a published-build/tool failure, not a busy-server timeout. The read-only library
and launcher scripts were not modified, and no global build or push was run. The saved
packet remains available for a retry after the published library is restored.

## Dispatcher retry validation, 2026-10-21

Started with the retained packet and the required `deliver2.py Q14
lem-weil-pbc-discrete-exchange-site-comparison --no-push`. It again exited 1 before
elaborating the delivered module: the overlay UniversalHomeomorphism import requires
`Mathlib/AlgebraicGeometry/Morphisms/Constructors.olean`, which the published library
lacks. Its server confirmation again reported `Live published library is unavailable`.
The direct prescribed `scompile.py` invocation on the saved module independently
returned exit 1 with exactly the same missing object and server confirmation.
Neither invocation timed out. There is no new module diagnostic to repair. Retained
all Lean and node files unchanged; no push, global build, live edit or launcher edit.


## Second reading by Q14

This is the resumed worker's self-check of the retained packet, not a claim of a
separate reviewer: the dispatcher explicitly forbids starting other agents. The
maintainer's independent review remains responsible for the external second reading.
I opened the current DAG statement, the saved declaration, and the full definitions of
baseChangeSourceComparisonIso, baseChangeTargetComparisonIso, the canonical derived
exchange and IsClassicalComplexFor. The saved Lean statement is retained.

The arbitrary discrete commutative ring is Λ with CommRing and no topology or finite
coefficient hypothesis. The four schemes, four arrows and ChosenCartesianSquare give
exactly the chosen Cartesian square. Only f and f' carry QuasiCompact and QuasiSeparated.
L is an object of the full bounded-below etale module derived category. A_T is the
existing exact comparisonUpperStar.mapDerivedCategory after Plus.ι. The source
comparison is the existing paste of leftDerivedUpperStarComparisonIso for g and
rightDerivedLowerStarComparisonIso' for f; the target comparison pastes the latter
for f' and the former for g'. They are NatIso values, so their types already supply
invertibility and naturality in L. Their definitions include the D+ inclusion
compatibilities. The equation composes the mapped etale exchange then T, and S then
the pro-etale exchange, in Lean composition order. The pro-etale exchange definition
is the canonical composition-comparison mate, with the derived edge adjunctions.
The four remaining conjuncts give the lower bound and all-degree continuity-map
classicality for each of the two displayed endpoints separately. No claim that an
exchange is invertible is introduced. No mathematical mismatch was found.

I rechecked identity edges, the zero complex, the zero ring, infinite rings and the
empty scheme: none is excluded by these binders. The common coefficient universe
is the upstream ModuleCat realization used by the exact comparison isomorphisms.
The currently recorded intrinsic and condensed interfaces are imported, with their
publicly retained ordinary constant-coefficient interfaces; no duplicate notion is
introduced. The module binds its only universe u and every variable explicitly,
contains one named theorem with its complete seven-step proof docstring, and has
only sorry as its proof. The current node had newer lean_audit metadata: I refreshed
all non-lean fields from the read-only checkout, retaining the original Lean record.
There are no new nodes, dependency modules, or mathematical statement corrections.


## Current retry diagnostics, 2026-10-21

The required first dry run progressed beyond the former missing Mathlib object, then
failed before this packet's elaboration: the private overlay compile of
WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic timed out after
60 seconds. That dry run's fallback reported Live published library is unavailable.
The subsequent direct prescribed scompile.py call hit the same overlay timeout;
its current-server confirmation rebuilt the prerequisite chain and independently
reported `WeilConjectures/Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean:
timeout after 60 s`. This is an actual upstream dependency compile timeout, not the
`no answer from the compile server` busy-server diagnostic. The draft has not yet
been elaborated, and no successful-compile or delivery claim is made. The upstream
module is read-only and is not owned by an item/dependency node in this delivery.
The compiler limit, launcher scripts, published sources and artifacts are unchanged.
The node signature was checked byte-for-byte against the theorem header and all
module lines are within 100 columns. The resumed report now records the required
self-check and the node preserves the current live non-lean metadata.


Final dry run after refreshing the node and adding the self-check also exited 1.
Its local overlay timed out on the same SheafCohomology.Basic module, and the server
confirmation ended with the same module's `timeout after 60 s`; it printed
`COMPILE FAILED on the server, nothing pushed`. The retained draft never reached
elaboration on any current attempt. No push was attempted.


## Current published-artifact failure, 2026-10-21

Started this retry with the saved report and the mandatory `deliver2.py Q14
lem-weil-pbc-discrete-exchange-site-comparison --no-push`. Its current diagnostic
is different from the earlier SheafCohomology.Basic timeout: the overlay compile
of `WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude` fails at its imports
in 0.6 seconds because the published object file
`WeilConjectures/Topology/Stratification.olean` does not exist. Its independent
current-server confirmation reports the same missing object file.

Ran the prescribed direct `scompile.py` on the retained module. In a newer overlay
snapshot it independently fails in 0.5 seconds on exactly the same missing object;
its current-server confirmation repeats that error. Also read the current server
source with `scompile.py --source WeilConjectures.Topology.Stratification`: the
source module exists and defines `Topology.Stratification` and
`Topology.Stratification.ofNoetherianSpace`. This is a missing published compiled
artifact, rather than a missing Lean notion or an elaboration timeout.

The draft uses the canonical source and target comparison isomorphisms from
`WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`; that module
imports the etale smooth-base-change framework and hence this prerequisite.
Removing it would leave the specified canonical comparisons unavailable.
A replacement definition under another module would duplicate the existing
stratification notion and would not supply the original imported module artifact.
No library, launcher tool or compiler limit was edited; no global build was run.
The authorized wrappers did not reach elaboration of the retained packet, and no
push or successful compile is claimed. The saved Lean module and node are retained.


## Final dispatcher retry, 2026-10-21

Inspected the retained packet and ran the prescribed dry run first. The saved node
has no non-lean difference from the current read-only DAG node. The signature is
verbatim, all lines are within 100 columns, every variable/universe is explicitly
bound, and the only proof is the named theorem's `sorry`. Reopened the current
source definitions of the canonical S/T comparisons, derived pro-etale exchange,
classical-complex predicate, chosen Cartesian square, and the blueprint pro-etale
paragraph and Stacks remark-base-change. The earlier clause-by-clause self-check
still applies; no statement correction or new notion is needed.

This dry run advanced past the earlier missing Stratification artifact and rebuilt
many upstream dependencies. It then failed before elaborating the delivered file:
local overlay `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`
reported `timeout after 60 s`. The independent current-server confirmation failed
in `WeilConjectures/AlgebraicGeometry/EtaleCohomologyFilteredColimit.lean` with
`timeout after 60 s`, and the delivery wrapper printed `COMPILE FAILED on the
server, nothing pushed` (exit 1).

Ran the prescribed direct scompile.py retry on the saved module. Its local overlay
again timed out after 60 seconds in the same CohomologyContinuity module, before
checking this delivery. This is an upstream file-compile timeout, not the busy-server
`no answer from the compile server` message. Both upstream source files are present
and read-only; changing launcher scripts, upstream sources or the compiler limit is
outside the authorized sandbox. Retained the canonical-comparison imports and the
saved theorem/node unchanged. No push or successful-compile claim is made.

The direct retry's current-server confirmation finally returned exit 1. It passed
EtaleCohomologyFilteredColimit in 48.4 seconds and rebuilt further prerequisites,
but stopped at
`WeilConjectures/AlgebraicGeometry/EtaleLimitCohomologyConnectingLadder.lean:
timeout after 60 s`. It never elaborated the delivered module. Thus the repeated
local failure and the independent server failures are in the upstream import
build, rather than this packet; neither is a busy-server no-answer return. No
push was attempted. All work remains in this sandbox for a later tool/build retry.


## Upstream definition diagnosis and delivery gate, 2026-10-21

Started with the retained packet and the required dry run. It failed before this
item's elaboration at the live upstream
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`, with the server
confirmation reporting the same 60-second timeout. The current server source was
read with `scompile.py --source` and agrees with the local read-only source
apart from a trailing blank line.

Unlike the previous attempts, this retry investigated the upstream computation
in sandbox source copies, using only the prescribed scompile.py wrapper. The
cohomology-triangle and cohomology-pullback maps, the sheaf cohomology map, and
`CategoryTheory.Abelian.Ext.instAddCommGroup` were tested with local irreducibility
controls. Temporary profiling/checkpoints and stronger conversion-transparency
settings were also tested. The stronger settings exposed concrete errors in the
existing proof's dependent cone rewrite, cocone identity normalizations and
implicit specialization of its local `key` lemma. A separate repair variant makes
those conversions explicit, including the opposite-index conversion. None of
these experiments is a successful clean-compile claim. The original item theorem
and its mathematical statement remain unchanged.

The unmodified-conversion-settings candidate is retained at
`lean/WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean` in this
sandbox. It keeps all original definition data and theorem signatures; its only
change is local irreducibility of the definitions above before the elementwise
continuity proof. Other experiments and their compiler output are under `scratch/`.
No live source, compiled artifact, launcher script or timeout was modified.

The dispatcher's latest instruction explicitly requires repairing the upstream
definition and delivering the repair. The required delivery wrapper cannot
package an upstream module: the next actual
`deliver2.py Q14 lem-weil-pbc-discrete-exchange-site-comparison --no-push` call
exited 1 immediately, before compilation/preflight, with:

```
FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean
```

The exact refusal is retained in `scratch/delivery-upstream-gate.log`. Moving the
file to a Sheaf module would not replace the original module imported by the
canonical comparison interfaces. Editing the read-only library or patching the
launcher wrapper is prohibited. This is the concrete packaging-tool refusal
preventing delivery of the authorized upstream repair, rather than a claim that
a compile timeout itself permits BLOCKED. No push has been attempted.

The final original-conversion-settings candidate also hit the 60-second local
file limit. After the definitive delivery-path refusal, I stopped its redundant
server-confirmation retry; no successful repair compile is claimed. All compiler
experiments started by this worker have ended. The blocker is the wrapper's
upstream-path refusal, not that timeout.


## Current packet retry, 2026-10-21

Started by reading the saved report and running the mandatory dry run on the
saved packet. It exited 1 immediately with the precise gate refusal:
`FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean`.
Preserved that upstream experiment, without changing its contents, at
`scratch/CohomologyContinuity-delivery-candidate.lean`, outside the delivery
module tree. No launcher or live source was changed.

Ran the mandatory dry run again on the remaining one-module statement packet.
It passed the initial path gate and attempted the compiler. The local overlay
waited for a concurrent compile, then returned exit 124 with
`overlay WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` and
`timeout after 60 s`. Its independent current-server confirmation returned
`WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean: timeout after 60 s`
and `COMPILE FAILED on the server, nothing pushed` (exit 1). This is an explicit
upstream file timeout, not the busy-server no-answer message.

Reopened the current item statement and dependency records, source/target
comparison definitions and classical-complex predicate. The saved self-check
still applies. Confirmed programmatically that the node signature matches the
module verbatim, every module line is within 100 columns, and the sole theorem
proof remains sorry. The saved node has no non-lean difference from the current
read-only DAG node; no item repair note is present. The Lean note now describes
these current diagnostics. No mathematical statement or definition changed.

The source import paths confirm this failure is needed by both canonical
interfaces: ProEtaleDirectImageComparison imports Comparison.LowerStarAcyclic,
which imports CohomologyContinuity; SmoothBaseChange imports Comparison, which
imports the same LowerStarAcyclic module. Removing the saved upstream experiment
therefore resolves the packaging refusal but does not allow the required
comparison interfaces to compile. Replacing them by duplicate definitions or
arbitrary maps would violate the statement contract. The compiler has not
elaborated this item and no delivery success is claimed.


## Definition diagnosis and current delivery-tool refusal, 2026-10-21

Started with the retained report and the prescribed dry run, before editing. That
one-module packet again failed in upstream CohomologyContinuity, locally and in
the independent server confirmation, before elaborating the item.

Continued diagnosis instead of treating the timeout as a tool failure. All source
experiments and logs are retained under scratch/. The following are distinct
results, not a claim that the continuity timeout has been repaired:

- `scratch/efficient*` restrict simplification and replace unconstrained rewrites
  with explicit triangle arguments. The tests exposed dependent-cone conversions,
  opposite-index identities and coerced cohomology-group conversions.
- `scratch/diagnostics.log` is a deliberately lowered-heartbeat diagnostic. It
  identifies repeated unfolding of CochainComplex.singleFunctors and
  HomologicalComplex.single (2552 reductions each at the 20000-heartbeat cutoff),
  through Ext and the cohomology group structures. No timeout allowance was raised.
- `scratch/rigid` and `scratch/rigid-clean` make those two constructions locally
  irreducible and repair the concrete cone conversion by applying congrArg to a
  subtype of commuting arrows. The final candidate has no diagnostic options,
  retains the original definition data and theorem statements, and contains no
  new sorry. It still times out in the full compile; it is NOT a validated repair.
- `scratch/mapopaque/lean/WeilConjectures/SixFunctors/Etale/UpperLowerStar/TopologicalInvariance.lean`
  makes the existing cohomologyMap definition no_expose, leaving its real data
  unchanged. Its existing cohomologyMap_apply characterization is exported with
  `by rfl` instead of a bare rfl term. This source patch DOES compile cleanly:
  `scratch/mapopaque-source.log` records 49.0 seconds for the sandbox check and
  46.2 seconds under the original module name; scompile.py exited 0. The external
  source search found no explicit unfolding of cohomologyMap to adapt. Testing
  continuity against that patch still times out, so this is a validated source
  patch, not a validated cure for the consumer.
- `scratch/opaque` also hides cohomologyTriangleMap, supplies its formula lemma,
  and adapts the two external source users that explicitly unfold it:
  CohomologyContinuity and EtaleRestrictedCohomologyNeighbourhoodColimit.
  The combined test does not compile cleanly; none of these extra patches is
  claimed as ready for landing.

Finally placed the cleanly compiled cohomologyMap source patch at its original
module path inside the delivery sandbox and ran the required delivery wrapper.
It exited 1 immediately, before compilation or preflight, with the exact refusal
retained in scratch/current-upstream-gate.log:

```
FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/SixFunctors/Etale/UpperLowerStar/TopologicalInvariance.lean
```

This is the actual tooling obstruction: the current instructions authorize
repairing the upstream definitions and adapting their users, but deliver2.py
unconditionally rejects every such upstream module path. Rehousing the same
existing definitions in a Sheaf module would duplicate them and would not change
what the original importing modules compile against. The wrapper is explicitly
not editable by this worker. No live source, launcher, compiler limit, build
artifact or Git state was edited directly. No push was attempted.

The gate-test copy has been removed from the delivery module tree; its exact
contents remain in scratch/mapopaque. All compiler experiments have ended.
The original one-module item packet is retained. Its signature remains verbatim
and its node has no non-Lean difference from the current read-only node. The
previous clause-by-clause second reading still applies. The unresolved consumer
compile is recorded honestly; the BLOCKED reason is the concrete upstream-path
refusal, rather than the 60-second timeout.


## Final retained-packet self-check, 2026-10-21

Read the saved report and ran the required dry run before changing the packet.
It passed both preflight and server compilation, with no item diagnostic to
repair. Retained the Lean module without alteration. Refreshed only the optional
lean.note to record current success; every non-lean node field matches the live
read-only node. The signature matches the module verbatim; no line exceeds
100 characters, autoImplicit is false, universe u and all variables are explicit,
and the sole theorem proof is sorry. No item repair note exists.

Reopened the node and the full S/T definitions in
WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange, together with
ChosenCartesianSquare, IsClassicalComplexFor, and the blueprint pro-etale
paragraph. The earlier clause-by-clause second reading remains valid: arbitrary
CommRing coefficients, four scheme arrows with chosen Cartesian identification,
qcqs assumptions on precisely f and f', and arbitrary bounded-below input L.
The canonical source and target NatIso values supply invertibility and
naturality in L. The equation uses the specified derived exchange and maps
the etale arrow through the fully faithful Plus inclusion and exact comparison.
The remaining conjuncts separately give a lower bound and classical cohomology
for each displayed pro-etale endpoint. No properness, coefficient finiteness,
torsion, Nontrivial or exchange-isomorphism assumption is introduced. Identity
edges, empty schemes, zero complexes, the zero ring and infinite rings remain
allowed. No statement correction, new node, dependency module or upstream
source patch was needed. This self-check is in-thread as required by the
dispatcher's prohibition on starting other agents; the maintainer supplies
the independent delivery review.
