## Worker report

`Sheaf.Paper.AmplificationProper` states
`AlgebraicGeometry.ProEtale.amplification_of_isProper` with proof `sorry`.
It asserts AMP(square; 2e), WIT(square), and TOW(square), using one square
and one arithmetic adic coefficient datum throughout. No mathematical statement
is corrected, and no new DAG node is introduced.

I read the item's full statement and six repaired proof steps, each statement
dependency and its Lean record, the recorded source declarations/docstrings,
and the blueprint source at order 1354 from the server literature copy. The
proof docstring follows the repaired DAG proof: in particular P_n need not be
perfect over P_{n+1}. The blueprint's older proof prose is not used to impose
that false condition.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `X' X Y' Y : Scheme.{u}` and `g' f' f g` have exactly the square's orientation.
  `sq : ChosenCartesianSquare g' f' f g` contains commutativity and the chosen
  identification with the fibre product, including both projection equations.
- `A`, `[CommRing A]`, `d : Scheme.AdicCoefficientDatum A` are the fixed adic
  coefficients implicit in the three named predicates. The datum retains the
  ideal, Noetherian ring, finite generation, torsion first quotient, and finite
  perfect positive quotients. There is no completeness or quotient flatness
  hypothesis. The coefficient size is the recorded site convention u+1.
- `[IsNoetherian X]`, `[IsNoetherian Y]`, `[IsNoetherian X']`, and
  `[IsNoetherian Y']` render all four Noetherian assumptions.
- `hDimX`, `hDimY`, `hDimX'`, `hDimY'` each say that the corresponding
  topological Krull dimension is bounded by some natural number. These are the
  four finite-dimensionality assumptions and permit empty schemes.
- `[IsProper f]` and `[IsProper f']` render both properness assumptions.
- `(N : ℕ) (hN : 0 < N)` is the positive annihilator. `hAnnihilator` is
  `∀ a : A ⧸ d.ideal, N • a = 0`, exactly N(A/I)=0.
  Specifying an arbitrary annihilator satisfying these hypotheses renders the
  source's existential wording: one applies the theorem to its witness.
- `hInvertX`, `hInvertY`, `hInvertX'`, `hInvertY'` require the image of N to be
  a unit in every local ring on each of the four schemes. This is precisely
  invertibility of the integer on each scheme.
- `(e : ℕ)` renders a nonnegative integer. `hFib` quantifies over all
  algebraically closed fields Ω and all geometric points `Spec Ω ⟶ Y`, and
  bounds the topological Krull dimension of `pullback f y` by e. No fibre
  nonemptiness or equidimensionality is assumed.
- `Scheme.HasFiniteLevelAmplification sq d (2 * e)` is AMP with the SAME
  bound 2e for f and f' and every positive quotient exponent. Its two FIN
  clauses retain the scheme/coefficient conventions as properties, rather
  than requiring new external hypotheses to form this predicate.
- `WitnessCompatibility sq d` is the recorded WIT, including compatible
  coefficient reductions, canonical composites, retained etale-origin data,
  and functorial transport on witnessed towers for all four functors.
- `Scheme.HasTowerPreservation sq d` is TOW. Its four quantifiers range over
  EVERY uniformly bounded constructible adic tower. Outputs retain quotient
  actions, evaluations, normalizations, transition compatibility, quotient
  cocycles, a common finite stratification, bounded adic-lisse local complexes,
  finite-lisse reduced cohomology, and reduction isomorphisms compatible with
  normalization and the AMP amplitude containments. This is preservation in
  D(Tow_A), before inverse limit; no arbitrary-tower finite-evaluation formula
  is added.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.Paper.CompletedAdicCoefficientDatum`,
  `AlgebraicGeometry.Scheme.AdicCoefficientDatum`, publicly reexported by
  `Sheaf.Paper.AdicCoefficientDatum`. The packet reuses this exact structure.
- `Sheaf.Paper.FiniteLevelAmplification`,
  `AlgebraicGeometry.Scheme.HasFiniteLevelAmplification` (the delivered Q08
  full-datum interface, described below).
- `Sheaf.Paper.WitnessCompatibility`,
  `AlgebraicGeometry.ProEtale.WitnessCompatibility` (existing recorded module).
- `Sheaf.Paper.TowerPreservation`,
  `AlgebraicGeometry.Scheme.HasTowerPreservation` (delivered Q08 interface).
- `Sheaf.Paper.BoundedConstructibleTower`,
  `AlgebraicGeometry.Scheme.AdicTower`, `AdicTowerLocalModel`, and
  `IsUniformlyBoundedConstructibleAdicTower` (existing recorded definitions).
- The convention dependency introduces no declaration. The statement uses
  Mathlib's Scheme, IsNoetherian, IsProper, topologicalKrullDim, IsUnit,
  presheaf stalks, algebraically closed fields, and categorical pullbacks.

Edge cases checked: e=0 leaves common bound zero; positive levels are indexed by
n : ℕ meaning exponent n+1 in the datum and TOW, so the first quotient is
included. The zero ring and I=A are allowed. N=1 is permitted when it
annihilates A/I. I=0 is allowed when the other arithmetic assumptions hold.
Empty schemes, empty fibres (dimension bottom), zero towers and empty finite
stratifications are not excluded. No condition on g or g' besides belonging to
the given square is added. All variables and universes are explicitly bound.

Searches made for an existing statement:

- msearch LeanFinder: "Proper base change square finite level amplification
  witness compatibility preservation bounded constructible adic towers";
  returned eight completion/adic-transition/quasi-finite-base-change results,
  none the conjunction of AMP/WIT/TOW.
- msearch Loogle: "AlgebraicGeometry.Proper, AlgebraicGeometry.Scheme";
  no hits, with unknown identifier AlgebraicGeometry.Proper. The actual proper
  predicate is Mathlib's IsProper, which is used here.
- msearch LeanSearch: "Proper pushforward preserves bounded constructible adic
  towers and finite torsion cohomological amplitude"; service unavailable
  (Internal Server Error), recorded as unavailable, no match verdict inferred.
- msearch Mathlib grep: `HasFiniteLevelAmplification|WitnessCompatibility|TowerPreservation`;
  no hits. Direct rg in upstream WeilConjectures and lean/Sheaf for the item id,
  `amplification_of_isProper`, and tower-preservation names found no existing
  theorem. Related proper constructibility and torsion bound statements were
  inspected; they prove components, not this conjunction.
- Current server source lookup for Sheaf.Paper.TowerPreservation reported source
  unavailable. A read-only delivery-branch inventory found the already delivered
  Q08 TOW packet (dry-run commit 75c0277fda), whose interfaces are reused here.

The theorem module publicly imports the statement's canonical TowerPreservation
and WitnessCompatibility interfaces, Mathlib properness, and algebraic closedness.
These contain the chosen square, coefficient datum, bounded tower notion and AMP.
The complete union of published proof-only imports currently fails with a duplicate
legacy pro-etale notation from UpperLowerStar.Defs versus the finite-coefficient
module used by this statement. Following the launcher's duplicate-import repair
instruction, those extra proof imports are deferred. The six-step natural-language
proof and all its named dependency references remain in the docstring and DAG.
Unstated proof-only prerequisites are not added as hypotheses.

## Dependency modules

The current base has no TOW record and no strict completed tower direct-image
or completed pullback record. The human's 2026-10-16 instruction requires
stating genuine prerequisites in this delivery. Before doing so I checked the
server sources and delivery branches; Q08 has already supplied exactly these
interfaces. This delivery reuses that packet rather than developing a competing
construction. All dependency node copies retain EVERY field except lean, whose
by/date and note identify this reuse. No source statement is changed.

`def-weil-pbc-adic-coefficient-datum`: Reuses the already delivered Q08 tower-preservation dependency packet (75c0277fda). Section 1(B): publicly reuse the recorded AdicCoefficientDatum structure from CompletedAdicCoefficientDatum, without redefining it. Its completed-coefficient constructions tie coefficient and scheme universes; this module supplies the same actual continuous-function limit and universal derived reduction construction for independent coefficient size t+1 on Scheme.{t}, retaining site object/Hom sizes t+1/t. No constant/completed coefficient identification is assumed. Compatibility repair: retain the prior public AdicLisseModule and ProEtaleFiniteModules imports and every existing AdicCoefficients declaration verbatim, including its constant comparison, finite quotient ring system, completed ring, residue module and normalized tensor sections, so CompletedConstantSheafReduction retains its original interface. Second reading: retain the entire published AdicCoefficients namespace; completedReductionCoefficient and quotient aliases now use its exact ringSystem with the full datum, and scalar extension aliases reuse completedAdicChangeData. No alternative coefficient sheaves are introduced. The declaration is `AlgebraicGeometry.Scheme.completedReductionCoefficient` in `Sheaf.Paper.AdicCoefficientDatum`.

`def-weil-pbc-completed-pullback`: Reuses the already delivered Q08 tower-preservation dependency packet (75c0277fda). This genuine prerequisite has no recorded Lean declaration. The module constructs the completed coefficient map from its finite projections and derives levelwise module pullback through its universal K-flat pair, before inverse limit. Ordinary and completed pullback and their normalized comparison are distinguished; finite evaluation is only asserted on reduction towers. The declaration is `AlgebraicGeometry.Scheme.completedPullbackObject` in `Sheaf.Paper.CompletedTowerPullback`.

`def-weil-pbc-constructible-direct-image-finiteness`: Reuses the already delivered Q08 tower-preservation dependency packet (75c0277fda). Section 1(B): the recorded identified-coefficient FIN API requires scheme/coefficient conventions as external parameters. TOW must be a predicate on arbitrary squares without new geometric hypotheses. This equivalent fixed-coefficient presentation packages precisely those conventions in HasFiniteCoefficientSchemeConventions and states constructibility of every nonnegative higher image and the same uniform vanishing bound. The declaration is `AlgebraicGeometry.Scheme.IsConstructibleDirectImageFinite` in `Sheaf.Paper.ConstructibleDirectImageFiniteness`.

`def-weil-pbc-derived-inverse-limit`: Reuses the already delivered Q08 tower-preservation dependency packet (75c0277fda). Reuse the existing Roos-triangle predicate exactly as the already delivered Q02 record does: C = D(Mod(A_T)), K n = ev_(n+1) M, with its actual derived tower transitions. This node chooses neither an object nor a functor, so no new limit-property definition is needed. The canonical derived tower sequence and transition helpers are included in the owning adic-datum module. Countable-product computation is the separately cited product theorem. The declaration is `CategoryTheory.IsDerivedLimitTriangle` in `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`.

`def-weil-pbc-finite-level-amplification`: Reuses the already delivered Q08 tower-preservation dependency packet (75c0277fda). Section 1(B): the recorded API requires Noetherian target instances, dimension bounds and invertibility proofs as external parameters. The TOW predicate must remain defined on arbitrary squares; this interface packages those identical FIN conventions within AMP rather than adding hypotheses to TOW. It uses the same canonically realized finite-coefficient categories and retains both pullbacks, every positive quotient and every interval. The declaration is `AlgebraicGeometry.Scheme.HasFiniteLevelAmplification` in `Sheaf.Paper.FiniteLevelAmplification`.

`def-weil-pbc-intrinsic-completion`: Reuses the already delivered Q08 tower-preservation dependency packet (75c0277fda). §1(B) coefficient presentation transport only. Publicly imports and reuses IntrinsicCompletionCompleted, whose ProEtaleAdicCoefficientDatum carries the same fields. Uses the canonical pbcCompletedComparison and exact restriction in both directions; the round trip is uniquely normalized as identity on sections. No second Koszul fiber, product or scalar-action definition is introduced. This makes the published construction usable with the bounded-tower continuous-function coefficients and preserves its explicit (u,0) unit. The declaration is `AlgebraicGeometry.Scheme.IsDerivedCompleteIntrinsic` in `Sheaf.Paper.IntrinsicCompletion`.

`def-weil-pbc-tower-preservation`: Reuses the already delivered Q08 tower-preservation dependency packet (75c0277fda).  The declaration is `AlgebraicGeometry.Scheme.HasTowerPreservation` in `Sheaf.Paper.TowerPreservation`.

`prop-weil-pbc-direct-image-limits`: Reuses the already delivered Q08 tower-preservation dependency packet (75c0277fda). This genuine prerequisite has no recorded Lean declaration. The module constructs sectionwise module direct image through the adjoint completed structure map, its levelwise strict-tower right-derived functor, the derived ordinary-limit comparison, intrinsic completeness, and the normalized finite projection-formula arrow. Second reading: explicitly state canonical Roos/product compatibility, quotient and reduction-unit naturality of the specified projection-formula maps, and the normalized completion-unit composite. These clauses were present in the dependency node but absent from its initial Lean interface. The declaration is `AlgebraicGeometry.Scheme.completedDirectImageRlimIso` in `Sheaf.Paper.CompletedTowerDirectImage`.

`prop-weil-pbc-rlim-functoriality`: Reuses the already delivered Q08 tower-preservation dependency packet (75c0277fda). Section 1(B): the newly recorded sequential interface uses scheme-sized coefficients and the CompletedAdicTowers presentation. This consumer retains independent coefficient size u+1 on the small site with object/Hom sizes u+1/u. The ordinary strict-tower limit and its universal K-injective right derived functor retain triangulatedness and invariance under resolution choice, with the canonical constant-tower unit. The declaration is `AlgebraicGeometry.Scheme.completedTowerRlim_properties` in `Sheaf.Paper.CompletedTowerDerivedLimitFunctor`.

The TOW packet's definitions contain actual data. Scalar extension choices
retain their universal counits and representative characterizations. Completed
coefficient maps come from finite projections; derived functors are determined
by their universal derived properties. Intrinsic completion transports the
published Koszul construction, rather than constructing another one. Generic
Roos-triangle notation is an existing declaration, not a replacement inverse
limit definition. Every postponed theorem is named and tagged to its owning
DAG node with a source and natural-language proof docstring.

Validation: all eight reused prerequisite modules passed scompile.py on current
server sources, with 60 seconds per file, nice 19, and two threads. The complete
existing AdicCoefficients namespace is byte-for-byte identical to the published
source. Main statement signatures and 100-character line bounds were checked.

The first complete import closure exposed the duplicate legacy notation while
compiling PullbackBoundedConstructible. Source inspection and pruning that module
plus the legacy comparison modules was insufficient: the union of remaining
proof-only imports also introduced the notation at the final theorem import.
The final module therefore uses the statement's canonical imports, as described
above. This is an import repair, with no hypothesis, conclusion, or definition
change. Local overlay artifact misses and one timeout on an imported module are
handled by the prescribed wrapper's server confirmation; no limit is increased.
The final required dry-run result is recorded after completion.

Elaboration repair: the geometric fibre is explicitly coerced to its point type,
`topologicalKrullDim ↥(pullback f y)`, so Lean uses the pullback in Scheme
rather than attempting the category of types. This retains precisely the same
geometric fibre and dimension bound; the node signature was refreshed verbatim.

Final theorem validation: after the explicit geometric-fibre coercion, the
required dry run compiled all nine modules and the existing-declaration probe
cleanly on the server. Preflight then rejected six supplied dependency nodes
as outside the item prerequisite closure, including completed-pullback and
direct-image-limits, which are explicitly in the unchanged item proof_deps.
The second-reading omission is expected for this worker; the other rejection
is being diagnosed as a validator inconsistency.

Validator diagnosis: tools/stage2_delivery.py _dep_closure stops its depth-first
traversal at len(seen) == 3000, before necessarily visiting even every direct
proof-dependency root. The full unchanged item prerequisite closure contains
11341 nodes. The root collection is a Python set, so the false
rejection depends on iteration order. The rejected completed-pullback and
direct-image-limits nodes are direct roots. No mathematical correction or
authorized Lean/node change repairs this validator condition. Tools are
read-only for the worker. A normal dry-run retry is being made.

Exact tool evidence: server tools/stage2_delivery.py, function _dep_closure,
uses `while todo and len(seen) < 3000:` after seeding `todo` from an unordered
set of the item's statement AND proof dependencies. Preflight printed:
"the node def-weil-pbc-completed-pullback exists on the base and is not in the
item's statement/proof prerequisite closure on the base or as delivered".
The unchanged item JSON directly lists that node, and
prop-weil-pbc-direct-image-limits, in proof_deps. A complete read-only DAG walk
finds all nine supplied dependency nodes inside its 11,341-node closure.
No delivery field edit is appropriate for this failure. The ordinary retry
uses the same compiling sources and records and changes no validator setting.

Final status: BLOCKED by the preflight tool defect, after the normal retry.
The retry again compiled all nine Lean modules and the existing-declaration
probe cleanly on the current server. It then rejected three genuine prerequisite
nodes (completed-pullback, constructible-direct-image-finiteness and
rlim-functoriality), causing three derivative module-owner failures. Unlike the
previous run, it accepted direct-image-limits, derived-inverse-limit and intrinsic
completion, confirming the ordering-dependent cutoff. The only other finding
is the expected missing second reading, which this worker must not fabricate.
No branch was pushed. Every source/module/node/report remains in the sandbox
for the second reader or a validator repair. No live source or tool was edited.

## Resumed worker check, 2026-10-16

Reopened the existing theorem, its seven statement-dependency nodes and recorded
interfaces, and the reused dependency packet. Read the blueprint order-1354 source
again from the server: its hypotheses and three conclusions agree with the theorem.
No statement or Lean source change was needed. All ten sandbox node copies differ
from the current shared base only in `lean`; the declaration signatures and line
lengths remain valid. The coefficient-record signature starts at `def`, omitting
only the preceding `noncomputable` modifier, as in the existing accepted format.

Repeated searches using the prescribed wrapper:

- Loogle `AlgebraicGeometry.IsProper, AlgebraicGeometry.Scheme`: twelve matches,
  including the properness class and its base-change stability, with no AMP/WIT/TOW
  assembly theorem. This corrects the earlier unsuccessful identifier query.
- LeanFinder `Proper pushforward preserves constructible adic towers with
  cohomological dimension at most twice geometric fibre dimension`: eight matches
  about constructible images and stability of scheme-morphism properties; none
  states the required conjunction.
- Mathlib grep `amplification_of_isProper|HasFiniteLevelAmplification|
  HasTowerPreservation|WitnessCompatibility`: no matches. Direct searches of
  upstream WeilConjectures and the shared Sheaf sources likewise found no existing
  `amplification_of_isProper` declaration.

The read-only server source still has `while todo and len(seen) < 3000:` in
`tools/stage2_delivery.py` `_dep_closure`. A new untruncated walk of the current
shared DAG reaches 11,354 nodes (the earlier 11,341 count was from its earlier
snapshot). All nine delivered dependencies are in this closure; completed-pullback
and direct-image-limits are still direct theorem dependencies. No tool source,
validator option, dependency statement, or DAG edge was changed to bypass the cap.

The prescribed fresh `deliver2.py --no-push` run completed. Its local compile
missed `completedTowerDerivedSequence` and `completedTowerDerivedStep` through the
older compiled transitive dependency; both definitions are present at the end of
the delivered `AdicCoefficientDatum.lean`. The wrapper automatically requested
current-server confirmation, with the normal per-file limits unchanged. All nine
Lean modules and the existing-declaration probe passed current-server compilation
without disallowed warnings.

The fresh preflight again failed solely on the known validator defect and the
expected absent second reading. Its ten findings were five incorrect dependency
rejections, four consequent module-owner rejections, and the second-reading check.
The incorrectly rejected nodes were:

- `def-weil-pbc-completed-pullback` (a direct proof dependency);
- `prop-weil-pbc-direct-image-limits` (a direct proof dependency);
- `def-weil-pbc-derived-inverse-limit`;
- `def-weil-pbc-intrinsic-completion`;
- `prop-weil-pbc-rlim-functoriality`.

For example, the tool again reported that completed-pullback "exists on the base
and is not in the item's statement/proof prerequisite closure on the base or as
delivered", contradicting the item's explicit `proof_deps` entry. The findings
differ from both earlier runs despite unchanged dependencies, consistent with
the traversal's unordered roots and cutoff. The source inspection, complete DAG
walk, and normal dry-run retry reproduce the failure without changing any tool
or validator setting. AGENTS.md section 3 prohibits working around or editing
these tools; this is an actual wrong refusal rather than missing mathematical work.

Final resumed status: BLOCKED by the persistent preflight traversal cap. No branch
was pushed, and no second reading was fabricated. All sources, node records,
search results and this report remain in the authorized sandbox.

## Resumed worker check, attempt 3, 2026-10-16

Rechecked the existing sandbox against the current shared DAG, the current server
blueprint source at order 1354, and the statement dependency declarations and
docstrings. The theorem retains every source hypothesis and all three conclusions.
All ten node copies differ from the shared base only in lean. All nine module
record signatures occur verbatim in their files; all modules disable auto-implicit
variables and have no lines over 100 characters. No Lean or node correction was
needed. No second reading is claimed.

Repeated LeanFinder search for proper-square amplification, witness compatibility
and constructible adic tower preservation returned eight related ring/base-change
and completion results, with no matching theorem. Loogle for
AlgebraicGeometry.IsProper, AlgebraicGeometry.Scheme returned twelve properness
results, with no matching conjunction. Mathlib grep for amplification_of_isProper,
HasFiniteLevelAmplification, HasTowerPreservation and WitnessCompatibility had
zero hits. Direct upstream and shared Sheaf searches found no existing theorem.
The prescribed server source lookup still reports Sheaf.Paper.TowerPreservation
unavailable, so its prerequisite packet remains necessary.

A full read-only traversal of the current shared DAG reaches 11,365 prerequisites
and includes every one of the nine supplied dependency nodes. Both completed
pullback and direct-image-limits are direct proof dependencies. Read-only server
source inspection confirms that tools/stage2_delivery.py still truncates
_dep_closure at 3,000 seen nodes. No tool, traversal option, or dependency edge
was changed to bypass that defect. The required fresh deliver2.py --no-push run
is in progress, including automatic server confirmation after the local overlay
missed the supplied completedTowerDerivedSequence/Step transitive declarations.

Attempt 3 result: all nine Lean files and the existing-declaration probe passed
server compilation without disallowed warnings. deliver2.py then built its
dry-run commit and ran current-server preflight. Preflight rejected exactly
one genuine prerequisite, prop-weil-pbc-direct-image-limits, as outside the
item statement/proof closure; this node is explicitly in the unchanged item
proof_deps. Its rejection caused the derivative CompletedTowerDirectImage.lean
module-owner failure. The third and final finding was the expected absent
second reading. Other nodes rejected by earlier runs were accepted this time,
again consistent with the unordered-root traversal and 3,000-node cutoff.

Exact diagnostic: "the node prop-weil-pbc-direct-image-limits exists on the
base and is not in the item's statement/proof prerequisite closure on the
base or as delivered". The tool also noted that its chosen base 965cd085c
had moved while compilation ran; it checked against that chosen base. This
is a repeated wrong refusal of an explicit direct dependency, not an absent
mathematical prerequisite. No module or node edit can legitimately repair the
validator traversal. No branch was pushed. Final status remains BLOCKED by
the persistent preflight tool defect; the full compiling packet is preserved
for the second reader after the maintainer repairs the validator.

## Resumed worker check, attempt 4, 2026-10-16

Reopened the worker and stage-2 rules, the example module, the theorem and its
statement dependencies, the current server blueprint source at order 1354,
and the actual finite-level AMP, WIT, bounded-tower and TOW interfaces.
The existing theorem retains the four schemes and chosen Cartesian square,
one adic datum, all four Noetherian and finite-dimensional hypotheses, both
properness hypotheses, the positive annihilator and its four invertibility
hypotheses, the geometric fibre bound, and exactly the AMP(2e), WIT and TOW
conjunction. No statement correction or source edit was necessary.

All ten delivered node copies still differ from the shared DAG only in lean.
All nine module signatures occur verbatim in their owning node records, all
modules disable auto-bound implicits, and all Lean lines satisfy the
100-character bound. The edge cases listed in the Worker report remain
included. No independent second reading is claimed.

Repeated prescribed searches: LeanFinder for proper-square amplification,
witness compatibility and constructible adic tower preservation returned
eight related base-change and adic-completion results, none the theorem.
Loogle for AlgebraicGeometry.IsProper, AlgebraicGeometry.Scheme returned
twelve properness declarations, none the conjunction. Mathlib grep for
amplification_of_isProper, HasFiniteLevelAmplification, HasTowerPreservation
and WitnessCompatibility returned no hits. Direct upstream and shared Sheaf
searches for the theorem declaration and item id returned no hits. Current
server source lookup still has no Sheaf.Paper.TowerPreservation, so the
existing prerequisite packet remains necessary.

Read-only current-server validator inspection again confirms the condition
`while todo and len(seen) < 3000:` in _dep_closure. A complete read-only walk
of the current shared DAG reaches 11,365 prerequisites and contains every
one of the nine supplied dependency nodes. The two previously rejected
completed-pullback and direct-image-limits nodes are explicit direct proof
dependencies. No tool, validator setting or dependency edge was changed.
The mandated fresh deliver2.py --no-push run is compiling the packet; after
the same stale local transitive-interface miss it automatically requested
current-server confirmation. Per-file limits remain unchanged.

Attempt 4 final result: current-server compilation passed all nine Lean
modules and the existing-declaration probe, with no disallowed warnings.
The wrapper built its dry-run commit and preflight returned five findings:
completed-pullback and rlim-functoriality were falsely rejected as outside
the item prerequisite closure; those rejections caused the two derivative
module-owner errors; the fifth was the expected absent second reading.

Exact direct-root diagnostic: "the node def-weil-pbc-completed-pullback
exists on the base and is not in the item's statement/proof prerequisite
closure on the base or as delivered". The unchanged item explicitly lists
def-weil-pbc-completed-pullback in proof_deps. rlim-functoriality is also
inside the uncapped closure verified above. The same packet accepted
direct-image-limits this time, which the preceding attempt had rejected.
This remains the reproduced unordered-traversal cutoff defect, not a missing
mathematical dependency or a module ownership defect.

No branch was pushed. All sources and node records are preserved. Final
status is BLOCKED by the current server preflight's 3,000-node closure cap;
AGENTS.md section 3 forbids worker edits or workarounds to this tool.


## Resumed worker check, attempt 5, 2026-10-16

Rechecked the theorem against its current DAG statement, all seven statement
dependencies and the actual square, coefficient datum, AMP, WIT, bounded-tower
and TOW declarations and docstrings. All ten sandbox nodes differ from the
current shared base only in lean. The nine delivered module signatures occur
verbatim in their records, all modules disable autoImplicit, and no Lean line
exceeds 100 characters. No mathematical or source correction was necessary.

Repeated the prescribed searches with the current wrappers: LeanFinder for
"Proper square finite level amplification witness compatibility preservation
of bounded constructible adic towers" returned eight adic-completion and
transition results, none this theorem. Loogle for
"AlgebraicGeometry.IsProper, AlgebraicGeometry.Scheme" returned twelve
properness declarations, none the conjunction. Mathlib grep for
"amplification_of_isProper|HasFiniteLevelAmplification|HasTowerPreservation|
WitnessCompatibility" returned zero hits. Direct rg of upstream WeilConjectures
and shared lean/Sheaf for the theorem and item id returned zero hits. The
prescribed current source lookup still reports Sheaf.Paper.TowerPreservation
unavailable, so the existing prerequisite packet remains necessary.

An uncapped read-only traversal of the current shared DAG reaches 11,365 nodes
and contains all nine delivered dependencies. Completed-pullback and
direct-image-limits remain explicit direct proof dependencies. The read-only
validator source still has `while todo and len(seen) < 3000:` in _dep_closure,
with unordered roots. No tool, validator setting, dependency edge or second
reading was changed to avoid this defect.

The fresh prescribed deliver2.py --no-push run is in progress. The local overlay
missed completedTowerDerivedSequence and completedTowerDerivedStep despite
their presence in the delivered AdicCoefficientDatum module; the wrapper
automatically requested current-server confirmation at the unchanged limits.


Attempt 5 final result: the prescribed fresh dry run printed
"OK (dry run): commit 5329ded73a compiles and passes the preflight except
for the second reading, which the second reader writes; nothing pushed."
All nine Lean modules and the existing-declaration probe passed current-server
confirmation without disallowed warnings. This run accepted all dependency
nodes; the only finding was the expected absent second reading. No module,
DAG edge, validator setting or tool was changed to obtain this result.

Final worker status: READY. The previously recorded BLOCKED statuses describe
earlier runs and are superseded by this successful dry run. No branch was
pushed, no second reading was fabricated, and the complete sandbox packet
is ready for the independent second reader.


## Earlier second reading (a previous round; superseded)

Independent reader, 2026-10-16. I did not author the statement or the reused
Q08 dependency packet. I opened the node, the blueprint source at order 1354,
the seven statement-dependency nodes, their actual declarations, all nine
supplied Lean modules, and the nine supplied dependency-node records. I also
read Stacks source labels lemma-cohomological-dimension-proper (095U),
theorem-constructible-shriek (0GL0), definition-Dbc (09C1),
lemma-describe-constructible-complexes (09C2), and
proposition-Noetherian-adic-constructible (09C7). The blueprint explicitly
assembles the three conclusions; the Stacks definitions are ingredients,
not a claim that this assembly is itself a Stacks theorem. In particular,
09C1 includes finite Tor dimension whereas the blueprint uses its separately
defined bounded constructible towers. I checked against those definitions,
without substituting D_cons for the blueprint category.

My object/hypothesis/conclusion inventory and comparison:

- Four schemes and arrows with Cartesian identification: the binders
  X', X, Y', Y : Scheme.{u}, g', f', f, g and sq : ChosenCartesianSquare
  g' f' f g have the required orientation. The dependency structure extends
  CommSq and has isoPullback, hom_fst and hom_snd; it provides the chosen
  identification as a square, rather than only commutativity. Pass.
- Fixed coefficients: A : Type (u+1), CommRing A and d :
  Scheme.AdicCoefficientDatum A give the one datum used in all conclusions.
  I opened its inherited CompleteCoefficientDatum: ideal, noetherian,
  finitelyGenerated, quotientTorsion and quotientPerfect, and the additional
  quotientFinite field. These are exactly the recorded arithmetic datum.
  No completeness, nonzero-ring, field or quotient-flatness assumption is
  added. Pass.
- Noetherianity of all four schemes: the four IsNoetherian instance binders
  cover X, Y, X', Y' individually. No assumption on g or g' is present. Pass.
- Finite dimension of all four schemes: hDimX, hDimY, hDimX', hDimY' are each
  an existential natural upper bound on topologicalKrullDim, in WithBot
  Nat-infinity. This includes dimension bottom for the empty scheme. Pass.
- Both proper arrows: IsProper f and IsProper f' are the two hypotheses in
  the node. Although properness of f' follows from the Cartesian square,
  retaining it faithfully reflects the node. Pass.
- Positive common annihilator: N : Nat, hN : 0 < N and hAnnihilator :
  forall a : A / d.ideal, N • a = 0 render the source's annihilator. The
  theorem takes an arbitrary witness to the existential source hypothesis;
  neither N nor its choice occurs in the conclusion. Pass.
- Invertibility on each scheme: hInvertX, hInvertY, hInvertX', hInvertY'
  quantify over every point and assert IsUnit of the natural-number cast
  in its actual local ring, the presheaf stalk. This is invertibility of
  the integer, with no characteristic silently excluded. Pass.
- Nonnegative fibre bound: e : Nat and hFib quantify over algebraically
  closed fields Omega : Type u and all Spec Omega -> Y, bounding the
  dimension of the scheme pullback of f by e. The explicit point-type
  coercion selects Scheme pullbacks. Residue fields and their algebraic
  closures can be taken in u, so this tests every geometric fibre of a
  Scheme.{u}; larger field extensions do not change its dimension. Pass.
- AMP(square;2e): HasFiniteLevelAmplification sq d (2 * e) uses the same
  datum, square and bound for both FIN clauses, at every n : Nat meaning
  exponent n+1. Its other two clauses are the actual exact finite pullbacks
  for g and g', preserving bounded constructibility and every [a,b].
  Additivity, shift and triangle preservation are those of the exact ambient
  mapDerivedCategory functor. The FIN conventions are packaged within the
  predicate, without additional formation-time hypotheses. Pass.
- WIT(square): WitnessCompatibility sq d is the recorded declaration. I
  opened PbcFamilyWitnessCompatibility, its reduction domain and witnessed
  tower structures: rho is natural on the full bounded constructible
  reduction domain; theta is exactly F(theta) after rho; the lift is a
  functor retaining origin pairs and their maps. Adjacent reductions extend
  by the recorded scalar-extension comparisons to all quotient chains.
  No AMP condition or output bounded-constructible restriction is added.
  All four families have the required source and target. Pass.
- TOW(square): HasTowerPreservation sq d uses the completed-coefficient
  strict derived tower operations before Rlim. Each preservation predicate
  quantifies over every uniformly bounded constructible AdicTower, and
  returns an AdicTower whose underlying object is isomorphic to the actual
  functor value. AdicTower retains quotient actions, evaluation isomorphisms,
  normalizations, transition equations and cocycles. The bounded predicate
  retains one finite stratification and common bounded adic-lisse finite-type
  local complexes, finite-lisse reduced cohomology and compatible reduction
  identifications. HasTowerAmplitudeCompatibleModels tests the actual
  finite-level operations and supplies models in the AMP intervals. Pass.

Dependency packet reading (H12/H13): no new DAG definition node is introduced.
Every supplied existing-node copy differs from the shared base only in lean.
I checked each module against its owning node, not only its name:

- def-weil-pbc-adic-coefficient-datum: preserves the published AdicCoefficients
  namespace, its continuous-component-function sheafification, quotient maps
  and actual inverse limit. The added strict reduction construction has
  canonical tensor-section transitions and a universal left-derived pair
  computed on K-flat representatives. Scalar extension reuses
  completedAdicChangeData/completedAdicDerivedChange and keeps the small-site
  object/morphism sizes t+1/t with coefficients in t+1. Balance, naturality
  and quotient cocycle clauses match the node; data are never sorry.
- def-weil-pbc-completed-pullback: c_g is the map into the limit specified
  by its finite projections. It is not required to be invertible. The
  strict pullback has the universal left-derived counit and objectwise
  K-flat characterization. The ordinary/completed comparison is made from
  the strict quotient unit and constant-tower comparison with their unique
  normalizations. Finite evaluation is stated for reduction towers only.
- def-weil-pbc-constructible-direct-image-finiteness: the canonical fixed-ring
  presentation has exactly constructible etale-origin sheaves, every q >= 0
  constructible higher direct image, and vanishing for every q > c with one
  bound. HasFiniteCoefficientSchemeConventions packages exactly the target
  Noetherian/dimension and additive-order invertibility conventions. This
  repairs the old interface's external assumptions without changing FIN.
- def-weil-pbc-finite-level-amplification: the two FIN clauses and the two
  exact pullback clauses range over all positive quotients and every closed
  cohomological interval. It uses the same canonical finite coefficient
  realization as the recorded bounded constructible category.
- def-weil-pbc-derived-inverse-limit: I opened the current server declaration
  CategoryTheory.IsDerivedLimitTriangle. It is precisely the distinguished
  triangle with the towerTransitionEndomorphism (1-shift); no new derived
  limit notion or arbitrary functor is substituted. The supplied derived
  evaluation sequence and step are the exact tower evaluations localized.
- prop-weil-pbc-rlim-functoriality: completedTowerRlim is the actual limit
  functor's universal right-derived functor on strict towers. Its properties
  include triangulatedness, invariance under universal derived pairs and
  the sequential Roos triangle. The constant-tower unit is uniquely fixed
  on representatives, rather than an arbitrary map to a selected cone.
- def-weil-pbc-intrinsic-completion: transports IntrinsicCompletionCompleted
  through pbcCompletedComparison and inverse exact restrictions. The
  uniquely section-normalized round trip preserves the existing explicit
  Koszul fiber and (u,0) completion unit; there is no second fiber definition.
- prop-weil-pbc-direct-image-limits: direct image uses the adjoint completed
  structure map, and its strict-tower functor is total right derivation of
  levelwise direct image. The evaluation comparison is canonical. The Rlim
  comparison derives the ordinary limit comparison. The packet includes its
  product/Roos compatibility with the connecting arrows, intrinsic
  completeness, the specified scalar-adjunction projection-formula mate,
  functorial invertibility, all quotient/unit compatibility equations and
  the normalized completion-unit composite. These cover every node clause.
- def-weil-pbc-tower-preservation: all four functors and the complete output
  data are as inventoried above. It neither restricts the preservation
  quantifier to reduction towers nor asserts a finite evaluation formula
  for arbitrary completed-coefficient towers.

H5/H6/H8/H9 checks: choice of data is through a universal derived pair,
a unique tensor/section formula, or an actual categorical construction.
No definition contains sorry data. Named postponed theorems have their
own source/blueprint tags and natural-language proofs and belong to the
owning node; theorem proofs remain sorry. All nine modules bind their
universes and disable autoImplicit. All ten recorded main signatures occur
verbatim in their files (the existing Roos predicate was read separately).
No target or natural-language node statement changed, so no statement_change
or citer audit is applicable.

Edge cases: the first quotient is index zero/exponent one, so no positive
level is lost. e=0 yields AMP with bound zero. Empty schemes and geometric
fibres satisfy their dimension bounds; invertibility over empty point types
is correctly vacuous. Zero rings, I=A and zero towers are included. I=0 and
N=1 are allowed whenever the actual datum/annihilator conditions hold.
Empty finite stratifications and the empty local site object remain covered.
Intervals include a=b and zero objects. No finite-freeness, fibre
nonemptiness, equidimensionality or extra characteristic assumption occurs.

Independent searches: prescribed msearch LeanFinder for "Proper morphism
geometric fiber dimension bound constructible higher direct image adic
inverse sequence amplification" returned eight fibre/properness/limit
results, none the conjunction. Loogle for "AlgebraicGeometry.IsProper,
AlgebraicGeometry.Scheme" returned twelve properness declarations, none
AMP/WIT/TOW. Mathlib grep for amplification, WitnessCompatibility and
HasTowerPreservation returned zero hits. Direct rg in upstream
WeilConjectures and shared lean/Sheaf for amplification_of_isProper and
the item id also returned zero hits. These searches used wording different
from the author's initial search. Current-server scompile --source reports
TowerPreservation unavailable, so the supplied prerequisite packet is still
needed; it reuses Q08's packet and the published canonical definitions.

Mismatch repaired: the main proof docstring had lost mathematical escapes,
leaving strings such as Nin, congnu and otimes. I restored readable membership,
isomorphism, tensor, witness and tower notation throughout the six proof
steps, retaining every step and named dependency. No signature, hypothesis,
conclusion, definition or node record required a mathematical change. The
independent inventory and dependency audit above are newly appended; the
Worker report and its historical validation notes remain in place.


Second-reader validation in progress: the explicit scompile.py call and the
required deliver2.py --no-push both use the prescribed per-file limits.
The local overlay reproduced the previously recorded stale transitive lookup
of completedTowerDerivedSequence/Step and automatically requested current-server
confirmation. A fresh uncapped read-only DAG walk reaches 11,365 prerequisites
and includes all nine delivered dependency nodes. Read-only inspection confirms
that the server validator still truncates _dep_closure at 3,000 seen nodes;
no dependency edge, random seed, tool or validator setting has been changed.


Second-reader dry-run result 1: all nine Lean modules and the existing-declaration
probe passed current-server compilation, without disallowed warnings. The tool
then made its dry-run commit and preflight rejected six actual prerequisites:
completed-pullback, constructible-direct-image-finiteness, derived-inverse-limit,
intrinsic-completion, direct-image-limits and rlim-functoriality. Five consequent
module-owner errors gave eleven findings in total. The second-reading check
passed. In particular completed-pullback and direct-image-limits are explicit
unchanged proof_deps of the item; all six are in the independently verified
11,365-node closure. The 3,000-node traversal cap, not an unauthorized delivery
file or a mathematical omission, causes these false rejections. A normal retry
is being run with the same mathematical packet and unchanged tool settings.


Second-reader dry-run retry result: all nine modules and the existing-declaration
probe again passed current-server compilation without disallowed warnings.
Preflight then returned exactly two findings: it falsely rejected
prop-weil-pbc-direct-image-limits as outside the prerequisite closure, and
consequently rejected CompletedTowerDirectImage.lean as having no owning node.
The unchanged item's proof_deps explicitly contains that node. The same retry
accepted the other five prerequisites rejected by the first run, confirming
the ordering-dependent 3,000-node cutoff diagnosed above.

Exact diagnostic: "the node prop-weil-pbc-direct-image-limits exists on the
base and is not in the item's statement/proof prerequisite closure on the
base or as delivered". This contradicts a direct unchanged proof_deps edge,
independently of any transitive traversal. The second reading is complete,
the signature is still verbatim, and the mathematical packet compiles. No
source repair or permitted node edit can fix this validator false refusal;
AGENTS.md section 3 prohibits editing or working around the tool. No branch
was pushed. Final second-reader status: BLOCKED by the persistent server
preflight traversal cutoff. Logs are retained in scratchpad/second-dryrun.log
and scratchpad/second-dryrun-retry.log; all reviewed sources and node records
are preserved for the maintainer's tool repair.

## Resumed worker validation after dispatcher retry, 2026-10-16

Reopened the contract, current node, all seven statement dependencies and their
recorded declarations, the saved theorem and dependency packet, and the prior
independent second reading. Read the exact order-1354 blueprint source again
from the server. Its four Noetherian and finite-dimensional schemes, two proper
maps, positive common annihilator invertible at every stalk, geometric fibre
bound, and AMP/WIT/TOW conclusions still match the theorem. No mathematical
statement, signature, import or dependency edge needs changing.

A fresh complete read-only DAG traversal reaches 11,365 prerequisites and
contains every supplied dependency node. The completed-pullback and strict
direct-image nodes remain explicit direct proof dependencies. All ten node
copies still differ from the shared base only in lean, and all nine file
signatures match their records modulo whitespace, with no line over 100
characters. The exact existing Roos-triangle declaration was reread using
scompile.py --source. TowerPreservation remains unavailable through that
source lookup, so its saved prerequisite packet is still necessary.

Read-only inspection of the current server validator reconfirms the unchanged
`while todo and len(seen) < 3000:` cutoff in `_dep_closure`. The prescribed
fresh dry run is logged in scratchpad/resumed-dryrun.log. Its local overlay
reproduced the stale transitive lookup of completedTowerDerivedSequence/Step,
and the authorized wrapper automatically requested current-server compilation.
No tool, validator setting, live file, random seed or DAG dependency was changed.
The existing independent second reading was preserved without alteration.

Final resumed result: the prescribed dry run completed successfully, exit 0:
`OK (dry run): commit 37fd741f27 passes the preflight and compiles; nothing pushed`.
All nine delivered modules and the existing-declaration probe passed the wrapper's
current-server compilation with no disallowed warning. The saved independent
second reading passed preflight. This supersedes the historical BLOCKED statuses
above; no Lean or mathematical node edit was required. The traversal cutoff
remains present, but this ordinary run accepted the complete packet. No seed,
setting, validator, source statement or dependency edge was changed. The tool
also preserved the current base's reviewed_lean metadata for the derived-limit
node rather than delivering that stale field from the sandbox copy.

READY for the second reader's delivery; no branch has been pushed by this worker.

## Second reading by Q21

I independently read the node statement, its recorded dependency signatures, the
AmplificationProper module, and the blueprint/source metadata. The item inventory
and verdicts are:

- The square is rendered by `X' X Y' Y : Scheme.{u}`, arrows `g' f' f g`, and
  `sq : ChosenCartesianSquare g' f' f g`; this supplies the displayed Cartesian
  orientation, commutativity, and chosen pullback identification. Pass.
- The coefficient datum is `{A : Type (u + 1)} [CommRing A]` and
  `d : Scheme.AdicCoefficientDatum A`; the same datum is used in all three
  conclusions. Pass.
- Four Noetherian hypotheses are the instance binders `[IsNoetherian X]`,
  `[IsNoetherian Y]`, `[IsNoetherian X']`, `[IsNoetherian Y']`. Pass.
- Four finite-dimension hypotheses are the existential natural bounds
  `hDimX`, `hDimY`, `hDimX'`, and `hDimY'` against `topologicalKrullDim` in
  `WithBot ℕ∞`. Pass.
- Properness is exactly `[IsProper f]` and `[IsProper f']`. Pass.
- The positive common annihilator is `(N : ℕ)`, `hN : 0 < N`, and
  `hAnnihilator : ∀ a : A ⧸ d.ideal, N • a = 0`; this is the source's
  existential witness written by elimination. Pass.
- Invertibility on all four schemes is rendered by the four pointwise stalk
  conditions `IsUnit (N : T.presheaf.stalk x)`. No characteristic restriction
  or nonempty-scheme assumption is added. Pass.
- The geometric fibre condition is `e : ℕ` and `hFib` over every algebraically
  closed `Ω : Type u` and every `Spec (.of Ω) ⟶ Y`, bounding
  `topologicalKrullDim ↥(pullback f y)` by `e`. Pass.
- The conclusion is the exact conjunction
  `Scheme.HasFiniteLevelAmplification sq d (2 * e) ∧ WitnessCompatibility sq d ∧
  Scheme.HasTowerPreservation sq d`, rendering AMP, WIT, and TOW in the source
  order with the common bound `2e`. Pass.

The dependency declarations were checked against their node records. The chosen
square, adic datum, finite-level AMP, bounded constructible towers, WIT, and TOW
interfaces are the recorded canonical declarations; no private replacement or
extra geometric hypothesis is used. Scheme conventions are correctly a
convention-only dependency. No new definition node or dependency repair was
needed.

Edge cases remain covered: `e = 0`, `N = 1`, zero rings and `I = A` when the
recorded datum permits them, empty schemes and fibres (bottom dimension), zero
or empty towers, and the first positive quotient (`n + 1`). The universe choices
match the scheme and coefficient conventions; no independent index universe is
introduced.

I repeated searches with alternate wording for proper base-change amplification,
finite-level amplification, witness compatibility, and tower preservation in
Mathlib, upstream `WeilConjectures`, and shared `lean/Sheaf`; no existing theorem
or duplicate notion was found. The source metadata confirms this is a blueprint
assembly of the cited Stacks/SGA ingredients rather than an existing Stacks
statement.

No mathematical mismatch was found and no Lean or node change was required. The
module has a source/blueprint docstring and a complete six-step proof plan, with
only the theorem proof postponed by `sorry`; all variables and universes are
explicitly bound.

Current-base update during this reading: Q31 has now landed the prerequisite
packet, and current `scompile.py --source Sheaf.Paper.TowerPreservation` succeeds.
The saved historical packet was therefore redundant and would replace newer
reviewed records, including the published-canonical AMP packaging. I moved all
eight dependency modules and all nine dependency-node copies out of the delivery
into scratchpad/superseded-dependency-packet. Only AmplificationProper.lean and
its owning node remain for delivery. The theorem signature, objects, hypotheses,
and conclusions are unchanged. It imports the newly landed canonical AMP/WIT/TOW
interfaces. No new node or dependency-module change is now delivered. This
supersedes earlier report claims that those modules are missing or necessary.

The renewed searches used LeanFinder query "proper direct image adic system
geometric fibre dimension constructible amplification compatibility" (eight
adic-completion/factorization hits, no theorem), Loogle query
"AlgebraicGeometry.IsProper, AlgebraicGeometry.Scheme" (twelve properness hits,
no assembly), and Mathlib grep for amplification_of_isProper, HasTowerPreservation,
WitnessCompatibility and HasFiniteLevelAmplification (zero hits). Direct rg in
upstream and shared Lean finds the expected canonical dependency definitions,
including newly landed TOW, and no existing amplification theorem.

I reread the exact blueprint order-1354 source and the cited Stacks .tex on the
server. The blueprint has precisely the node's statement. Tag 095U requires a
proper map and fibre dimension bound for its torsion vanishing result; 0GL0
has separated finite presentation and qcqs hypotheses, supplied here by proper
maps between Noetherian schemes. Tags 09C1/09C2 concern finite Tor dimension in
D_cons, whereas the blueprint's bounded constructible tower is its explicitly
separate notion; its extra common local model clauses are retained by the landed
TOW predicate. No Tor-dimension assumption is silently added to this theorem.

Final dependency reading on the newly landed base: I opened
ChosenCartesianSquare's isoPullback/hom_fst/hom_snd fields, CompleteCoefficientDatum
and AdicCoefficientDatum's arithmetic fields, the published finiteCoefficient
amplitude and pullback predicates, the new existential AMP wrapper, the
PbcFamilyWitnessCompatibility rho/lift/object/map/normalization equations,
AdicTower's level/evaluation/normalization/transition/cocycle fields,
AdicTowerLocalModel's term bounds/adic-lisse/finite-lisse/identification/compatibility
fields, and TOW's four preservation clauses. These are exactly the notions
listed in the inventory. The landed AMP wrapper reuses the published coefficient
categories and operations, so removing the old packet also removes its duplicate
fixed-coefficient helper predicates. The main theorem still requires no edit.

Final isolated compile: `scompile.py Q21 thm-weil-pbc-amplification-proper
lean/Sheaf/Paper/AmplificationProper.lean` exited 0 against the newly landed
dependencies, locally in both sandbox and library modes, with no warnings or
errors (9.2 seconds and 6.2 seconds). The node's lean.statement is verbatim the
file signature; only its lean field differs from the current base. All Lean
lines are within 100 characters.

Final dry run: the prescribed deliver2.py --no-push exited 0 and printed
`OK (dry run): commit d6823e126e passes the preflight and compiles; nothing pushed`.
Its staged set was exactly the report, the owning node record, and
lean/Sheaf/Paper/AmplificationProper.lean. The old prerequisite-closure cutoff
problem is irrelevant to this reduced delivery; no tool or validator workaround
was used. Delivery follows with the same mathematical packet.
