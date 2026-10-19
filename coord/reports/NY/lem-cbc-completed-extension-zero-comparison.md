## Worker report

Stage 1 repair for NY, item `lem-cbc-completed-extension-zero-comparison`, 2026-10-16.
This submission contains a natural-language split, not a Lean binding. The current
brief, GOAL.md and coord/brief-stage1.md prohibit Lean writing and compilation.
The maintenance return asks for a stage-2 interface repair; that part remains a
separate stage-2 obligation. Nothing here certifies that the published Lean factors
compose or that the target worker may resume stage 2.

Files written:

- `dag/nodes/sec-smooth-purity/lem-cbc-completed-extension-zero-comparison.json`:
  existing statement, split into eight proof steps; no Mathlib match.
- `citations.json`: 48 verbatim statement excerpts, one for every step citation.
- `report.md`: this report, replacing a mixed stage-2/stage-1 historical report.
- `searches.jsonl`: appended only by the prescribed msearch.py commands.

No new DAG nodes or Mathlib leaves. The inherited Lean module and consumer remain
untouched historical sandbox material; deliver.py packages no Lean files. The old
report is saved under `scratchpad/repair-stage1/report-inherited.md`. The node's
stale `lean` field was removed to agree with the shared node, which has no current
binding. Maintainer fields were refreshed from the shared JSON, without changing
unit/chapter metadata, statement, hypotheses or statement dependencies.

Attachments: none. Searching all of the slopmaster2 WeilConjectures tree for the
item tag, `completedExtensionZeroComparison` and `cbcCompletedExchange` returned
no declaration. Concept searches found ordinary open-extension constructions and
adic realization results. The latter include sorry declarations and use another
category/API; they do not give every clause of this item. In particular the source
`SixFunctors/ProEtale/TraceFormula/Adic.lean` assumes additional adic/domain and
realization data and contains `sorry` at its completion/tower assertions. It is not
an attachment. The published side theorem also has `sorry` and the withdrawn
presentation described in the return, so cannot be attached.

WANTED: none; all sources used by this split are present locally.

What was wrong: the inherited report called this a delivered stage-2 repair and
claimed compiler validation, while the current task is stage 1. I have not verified
those historical compiler claims and make none here. The current shared node is
`unsplit`, despite retaining an older review record. I compared its mathematical
fields with the sandbox: the statement and dependency route agree. The retained
Step 4 binder and signed homotopy correction in Step 5 were preserved. New work
in Steps 7-8 writes the actual coefficient-map projection equations, the natural
identity-on-tensors comparison, the universal derived counit equation and the
constant-tower quotient-unit compatibility. A new citation of the existing
`lem-pur-left-derived-from-kflat-class` supplies exactly that universal pair; no
new node moves the item's conclusion elsewhere.

## Maintenance return: scope and disposition

I read the full dedicated return, the archived binding
`coord/reports/maintenance/def-cbc-completed-exchange-map.invalidated-lean.json`,
and the relevant constructions in the four requested published modules:

- `CompletedPullback`: `d.completedPull` is reduction, `d.towerPull`, then
  `completedRlim`; `ordinaryToCompleted` uses the constant-tower adjunction and
  actual quotient augmentation.
- `CompletedTowerPullback`: finite projection maps define `completedCoefficientMap`;
  `completedModulePullback` uses it for scalar extension; the universal tower and
  ordinary derived pairs expose actual K-flat counits and quotient-unit normalization.
- `CompletedExtensionZeroComparison`: `cbcCompletedPullback` instead uses
  `completedTowerPullback` and `completedTowerRlim`; `cbcCompletedExchange` and the
  theorem have that presentation. Its ordinary exchange is the inverse of the
  derived underived adjoint mate, with a stated K-flat counit equation.
- `CompletedBaseChangeMap`: `d.completedExchange` really ends in proper pushforward
  of `d.completedPull`, not of `cbcCompletedPullback`.

The defect is real: the old signature alone is not the required consumer interface.
The stage-1 proof now explicitly starts with the recorded coefficient structure map,
compares finite coefficient maps and every quotient arrow, and fixes any change of
presentation by the actual universal derived counits. Step 8 compares the specified
ordinary-to-completed units using the strict quotient augmentation, instead of
asserting that isomorphic endpoints suffice. It retains the finite inverse adjoint
mates, the quasi-compactness of j, intrinsic completeness and arbitrary base change.
No extra comparison hypothesis or claim that the two Lean functors are definitionally
equal is used. The old public API has not been changed.

Still to do in stage 2: publish and independently review an actual natural transport
or comparison on `d.completedPull`, retaining the normalization equations and old
API, and compile a consumer of the proper and open factors with no added hypotheses.
No consumer was compiled in this run. The old retained module is not a usable reviewed
binding merely because it is present in the sandbox, and no `existing: true` alias or
new `lean` record is submitted. The stage-1 dry run below does not discharge this
stage-2 obligation.

## Source error

STATEMENT-DISPUTED (inherited correction, retained): the blueprint's arbitrary-open
parenthetical calls sheaf extension by zero sectionwise extension by zero and infers
product preservation. Stacks `proetale.tex`, Tag 09BP, label
`lemma-j-shriek-limits`, instead assumes a quasi-compact open immersion and uses a
kernel/recollement argument. The current node already includes this correction;
this repair does not weaken or otherwise change its statement.

For the obstruction to dropping quasi-compactness, take
X = Spec(product over m >= 1 of F_2), with U the union of the isolated principal
points, A = Z_l and I = (l). U is discrete and not quasi-compact. A global section
of j!A_U has finite support on these points: local presentations through the
extension presheaf give support in U, and the quasi-compactness of X gives a finite
refinement. The compatible sections (l^m mod l^n)_m have finite support at each n,
but their inverse-limit family has infinite support. They therefore give a section
of lim j!(A/l^n)_U absent from j!A_U. The complete A_U need not have complete
extension by zero. The node's existing quasi-compactness and completeness clauses
are necessary to keep its completed pullback input in its stated domain.

The unit route remains finite coefficients followed by strict derived limits. The
only replaced source inference is the invalid parenthetical: Steps 4-5 give the
09BP kernel proof with the hypothesis it actually requires. No SGA source is used.

## Not duplicates

No new nodes. The whole-blueprint search `blueprint_refs.py search 'completed extension'`
found the item and `def-cbc-completed-exchange-map`; the latter defines the
proper-plus-open composite and does not prove the open factor. The ancestor search
identifies this item itself as its nearest blueprint ancestor. The resolving-class
node was found and its statement read before citing it; it is reused unchanged.
There are no new same-tag pairs to distinguish.

## Mathlib searches

All additional Mathlib searches were made through msearch.py, and the exact queries
and returned names are retained in searches.jsonl and mathlib_searches:

- LeanFinder, `Canonical completed pullback comparison with extension by zero for a quasi-compact open immersion`:
  eight hits about geometric pullbacks and scheme-module restriction, with no
  completion, strict towers or completed extension-by-zero theorem.
- LeanSearch, `Completed pullback commutes with extension by zero along a quasi-compact open immersion on the pro-etale site`:
  eight hits about zero hypercovers, quasi-compact covers and geometric open pullbacks.
  This invocation succeeded; it is not recorded as unavailable.
- Loogle, `"extensionByZero"`: zero hits.
- Mathlib grep, `Roos|derivedInverseLimit|homotopyLimit|lowerShriek`: zero hits.
- Second LeanFinder phrasing, `An exact additive functor commuting with countable products preserves the homotopy inverse limit of a tower of complexes`:
  eight general homological-complex factorization, homotopy and exact-functor hits;
  none supplies the sequential derived-limit or completed open exchange statement.

The older unavailable results remain historical searches; no unavailable service
was treated as an absence result. No search not actually run is newly recorded.

## Review by NY

I read the current main-20261015 blueprint statement and proof under
`sec-six-functors-basics/sk-prop-sf-cbc`, together with the imported chapter and unit
records. The node retains its historical chapter/unit binding. The current unit
also restricts its coefficient claims and uses finite reductions then derived
limits; this split follows that route. Its `blueprint.is` is the item itself,
`same_as` remains empty, and split_report.blueprint maps all eight steps to the
source proof, including the corrected final parenthetical.

I checked the eight statement dependencies against the actual statement. The datum
supplies Noetherian A, torsion A/I and finite perfect positive quotients. The open
square supplies both opens and cartesianness, with arbitrary g. Quasi-compactness is
the earlier recorded correction. Slice restriction identifies completed limit
sheaves, not completed modules with discrete A-modules. The presheaf extension and
its module sheafification define j!. Intrinsic completeness means invertibility of
the specified Koszul unit. The completed-pullback definition uses the finite-projection
structure map, strict derived tower functor and specified ordinary-to-completed unit.
No hypothesis was added or removed in this repair.

Step 1 uses the datum, open-square definition, weakly-etale localization, sectionwise
module limits and quasi-compact base change. I read these statements and Stacks
01K5 (`schemes.tex`, `lemma-quasi-compact-preserved-base-change`). The componentwise
identity of compatible families proves the ringed restriction and projection
compatibility. Base change gives quasi-compact j' without any condition on g.
The elementary assembly uses no hidden preservation theorem.

Step 2 uses the general ringed-site restriction/extension adjunction, the exact-functor
passage to derived categories, the finite extension theorem, and the extension,
scalar-restriction and module-sheafification definitions. Stacks 03DI and 03DJ in
`sites-modules.tex` explicitly give the sheafified direct-sum construction, adjunction
and exactness. The general node covers the possibly nonfinite completed ring sheaf;
the finite node is used only for P_n. Composing the scalar action changes none of
the underlying summands or the abelian sheafification, which proves the additional
scalar-restriction comparison rather than assuming it.

Step 3 uses K-flat resolutions with flat terms, the ringed-slice tensor comparison,
left-adjoint colimit preservation, and the tensor-complex, K-flat and flat definitions.
I checked 06YS (`sites-cohomology.tex`, `lemma-K-flat-resolution`) and 0E8I
(`sites-modules.tex`, `lemma-j-shriek-and-tensor`). Exact restriction takes acyclic
complexes to acyclic ones; tensor with P and exact extension then prove K-flatness
of e!P. The same argument for a flat term proves flatness of its extension. Direct
sums in totalization are preserved because e! is a left adjoint. The generator
formula with q_{b,a} checks every actual reduction transition. It does not use
exactness alone to assert tensor/reduction compatibility.

Step 4 uses the existing closed-subscheme existence theorem, direct-image formula,
slice localization, quasi-compact ringed recollement, sectionwise limits and the
closed-immersion all-limit theorem. I checked 09AA (`lemma-closed-immersion`) and
09BP (`lemma-j-shriek-limits`) in proetale.tex. For H=e_*F, restriction gives F;
recollement therefore gives e!F as the stated kernel. Both direct images preserve
products sectionwise; closed inverse image preserves them with the correct target
i^{-1}R. Kernels of coordinate maps are coordinatewise kernels, including an empty
product. This is the elementary kernel assembly from those statements; there is
no false sectionwise-zero description.

Step 5 uses exact countable module products, derived-product representation, the
levelwise abelian tower category, the current exact-functor/Rlim theorem, ringed
strict-tower homotopy limits, functorial Rlim, the K-injective Roos-complex theorem,
Grothendieck module categories and enough injectives. I read every statement, and
07KC (`derived.tex`, `lemma-products`). Exact products apply to the completed ring
sheaves. Products of towers are constructed levelwise in the step; exactness is
then levelwise. The Roos-complex node actually supplies the kernel inclusion
quasi-isomorphism for an arbitrary K-injective tower. It is not replaced by 070M,
whose `lemma-difficulty-K-injectives` concerns a particular truncation tower.
The coordinate change (y,x) -> (x,-y) gives the displayed fiber differential.
I checked the signed homotopy (hx,-hy), the natural kernel inclusion, theta and
kappa, and the two Roos equations. The current exact-functor/Rlim node guarantees
invertibility of a specified compatible map, not uniqueness or canonicity; the
explicit construction is retained for precisely this reason.

Step 6 uses the intrinsic-completion definition, ringed-slice tensor theorem and
completed-pullback reduction theorem. I read 0A0E (`algebraization.tex`,
`lemma-derived-completion-koszul`) for the model and 099N (2),(5) for the route.
Restriction preserves the finite free Koszul terms and their multiplication
transitions; Steps 3-4 preserve the actual fiber differential and its unit
c -> ((c tensor 1)_m,0). This proves completeness of j!K before completed
pullback is applied to it. The reduction theorem then applies separately to g_U
and g; extension along quasi-compact j' gives the final endpoint's completeness.
The proof uses the stated complete-input hypotheses at both applications.

Step 7 uses the datum, finite constant exact pullback, finite open base change,
site composition, extension-presheaf and ringed adjunction definitions, inverse
image, completed pullback, constant-completion equivalence, and the newly cited
resolving-class theorem. The finite open theorem gives the whole complex-level
canonical comparison. Its inverse is the adjoint mate of the summand-inclusion
unit; site composition is explicitly compatible with the adjunction. Scalar
restriction preserves these abelian maps, giving every quotient transition.
The constant-completion equivalence states the finite-reduction comparisons and
their transition compatibility; the balanced tensor formula verifies the
rebracketing. For the new normalization paragraph I checked 06XN, 05SE and
`equation-everywhere` in derived.tex and opened the resolving-class node: its
statement supplies an everywhere-defined universal left-derived pair with
invertible counits on the resolving class. Universal maps in both directions
have identity composites by that universal property. This proves the stated
counit-normalized comparison, rather than assuming an arbitrary endpoint
isomorphism. It is declared as an off-unit generic tool in split_report;
maintainer-owned accepted tool_uses was not extended by this worker.

Step 8 uses functorial Rlim and the completed-pullback definition, together with
the constructions in Steps 3, 5-7. The first arrow is literally Rlim of the strict
finite exchange, and the second is the inverse of the explicitly normalized
lambda. The definition supplies both source and target; Step 6 checks their
domains and completeness. For the added unit check, quotient augmentation is
x -> x tensor 1 and every transition preserves it. The coefficient/tensor and
counit comparisons therefore preserve the constant-tower augmentation; naturality
of the specified constant-tower/Rlim unit identifies the ordinary-to-completed
maps. In the fiber model the compatible family maps to (x,0), agreeing with
lambda. The retained finite inverse mates are unchanged. This explains the
mathematical normalization a future stage-2 interface must implement; it does
not claim the published Lean normalizations have been proved or reviewed.

B-E audit: there are no new nodes, so no new statement-only, duplicate, clause
relabeling or Mathlib-leaf obligations. All cited statements were opened, including
the added universal-pair theorem. All 48 citation quotes are verbatim statement
text. Proof dependencies are exactly the union of step uses. The proof adds no
smallness beyond the fixed site/tower universes, no affine-intersection assumption,
no finite-type or quasi-compactness assumption on g, and no invertibility assumption
on the completed coefficient structure map. TeX and source tag/label references
are retained. This is a proof in steps, not an application of a newly renamed
version of the whole assertion.

Edge cases checked: zero objects and the zero coefficient ring, empty open and
empty schemes, identity open and identity base change, I=0 with the empty generator
tuple, and arbitrary non-quasi-compact g. The positive quotient indexing avoids an
unintended P_0. For I=0 the tower is constant and the given fiber unit recovers C;
no positive number of generators is needed. The projection and unit equations
still hold for identity base change and zero modules. There is no new statement
requiring a separate counterexample search.

## Retry audit by NY — 2026-10-16

This retry compared the retained sandbox JSON with the current shared node without
running git in the shared repository. The current node is still unsplit and its
Lean binding is still null. The statement and statement dependencies agree exactly;
the retained changes are in the proof, proof origin, proof dependencies, search
records, split report and status. No finished live split was overwritten.

I reopened the current main-20261015 statement and proof, the chapter/unit records,
the archived invalidated binding, and the relevant definitions and normalizations
in CompletedPullback, CompletedTowerPullback, CompletedExtensionZeroComparison and
CompletedBaseChangeMap. The archive's alleged binding really uses cbcCompletedPullback.
The proper factor really uses d.completedPull. The universal-pair argument in
Steps 7–8 specifies the mathematical normalization a future interface must satisfy;
it is not evidence that those two published Lean presentations have already been
connected. The maintenance request to publish and compile that interface remains
unfulfilled under this run's explicit stage-1-only restriction. Neither the retained
Lean file nor its historical consumer is delivered or used as an attachment.

For the new normalization citation I reread the complete statement of
lem-pur-left-derived-from-kflat-class: it supplies a universal derived pair and
invertible counits on the resolving class, exactly what Step 7 uses. I also reopened
every other cited node's statement. Step 4 uses the ringed recollement kernel with
its quasi-compact-open hypothesis; Stacks proetale.tex, lemma-j-shriek-limits and
lemma-closed-immersion confirm that argument. Step 5 uses the explicit K-injective
Roos quasi-isomorphism, not an arbitrary choice of cone map. Steps 7–8 preserve the
finite projections, quotient transitions, K-flat counits and quotient augmentations.
In particular neither step assumes that the completed coefficient map is invertible.
There is still no added hypothesis on g. I retained the existing empty-open,
identity-square, zero-complex and I=0 checks; the formulas reduce to the zero or
identity maps in those cases.

A fresh read-only audit verified all 48 step/node quotes verbatim, exact equality
of proof_deps with the union of uses, and 1,013 reachable nodes without a missing
node or dependency cycle. A whole-blueprint search for 'completed extension' again
found only this item and the definition of the proper-plus-open composite; the
latter is not a proof of this open factor. No new nodes were created.

Four fresh msearch.py calls are recorded exactly in searches.jsonl and the node:
LeanFinder, 'Completed pullback commutes with extension by zero for a quasi-compact
open immersion on a pro-etale site' (eight geometric pullback hits); Loogle,
'"extensionByZero"' (zero hits); grep,
'completedPullback|completedPull|lowerShriek|extensionByZero' (zero hits); and
LeanSearch, 'An exact functor preserving countable products commutes with derived
inverse limits of strict towers' (eight exact-functor/finite-limit hits). I read
all returned signatures. None states the item or gives a one-line specialization;
no successful service was recorded as unavailable or vice versa. The earlier
second-phrasing searches remain in the log. This retry wrote no Lean, ran no
compiler and changed no shared project or launcher file.

## Validation

The read-only dependency audit traversed 1,013 reachable nodes with no missing
dependency or cycle findings. All 48 verbatim citations, the unchanged statement
and statement dependencies, and the exact proof-dependency union were checked.
The required mechanical validation command is:

`python3 /home/ubuntu/weil-launcher-nt/deliver.py NY lem-cbc-completed-extension-zero-comparison --no-push`

Its stdout is the authoritative dry-run outcome; READY is permitted only after
`OK (not pushed)` and successful preflight. The initial invocation waited for a
slot in the shared delivery-worktree pool, before any preflight output. No push,
compiler, Lake, global build, live source edit or launcher edit has been performed
in this run. The historical stage-2 module is excluded from the stage-1 delivery.
Stage-1 preflight does not certify a usable reviewed stage-2 binding.


## Previous dry-run blocker

The required `deliver.py NY lem-cbc-completed-extension-zero-comparison --no-push`
produced no stdout/stderr or preflight result during ten minutes of waiting.
Read-only process inspection showed it remained in `_reserve_worktree_slot`,
with only its group-lock file open and no reserved slot. All of the default
48 pool slots were occupied at the pool inspection. I stopped only my own
waiting delivery process with SIGTERM after this wait; a resulting exit 143
is that deliberate cancellation, not a compiler/preflight rejection or a push
attempt. No temporary delivery worktree was allocated by this invocation.
The required current dry run has therefore not printed OK. The repaired
node, report, actual searches and 48 verified citations are retained in this
sandbox. No launcher code, lock, shared repository or other process was changed.
The next reader must rerun the dry run once the shared pool is available.
The separate stage-2 reviewed-interface requirement also remains open, as
explained above; this stage-1 run wrote and compiled no Lean.

## Current retry: delivery tool blocker

The required no-push delivery was run again in this retry. After 04:09
(approximately four minutes), it still had no stdout/stderr or preflight result.
Read-only inspection found this invocation waiting on deliver-NY.lock, with no
worktree slot or temporary worktree allocated. The lock holder was a different
NY delivery, det-pe-weak-contractible-equivalences, which itself had waited over
twelve minutes and held a worktree slot while waiting on the shared newtargets
fetch lock. This retry did not alter that process, any shared lock, the launcher,
or the shared repository.

After confirming its exact command and open files, I stopped only this retry's
waiting delivery process with SIGTERM. Its cancellation is not a preflight
rejection. The mandatory dry run has not printed OK, so READY is not justified.
The stage-1 split, 48 validated citations, genuine search log and updated report
remain in this sandbox. No delivery was pushed and no Lean file was edited or
compiled. A later reader must obtain an actual no-push preflight result before
delivering; the distinct maintenance request for a reviewed stage-2 transport
and consumer remains deferred, as stated above.

## Final dry run

After the shared NY delivery lock became available, the required command
`python3 /home/ubuntu/weil-launcher-nt/deliver.py NY lem-cbc-completed-extension-zero-comparison --no-push`
completed successfully at 2026-10-16 with:

`OK (not pushed) deliver/NY/lem-cbc-completed-extension-zero-comparison at ac6620d694: preflight passed`

This is the current accepted stage-1 sandbox state. The prior blocker notes above
record only earlier attempts and are superseded by this successful run. No Lean
file was written or compiled, and no delivery was pushed.

## Second reading by NY

I reread the current main-20261015 blueprint statement and proof, the imported node, and every statement dependency. The item statement agrees with the source's finite-reduction/derived-limit route after the inherited quasi-compactness correction; the correction is recorded under `## Source error` and tested on the non-quasi-compact discrete-open example. There are no new nodes, so B1–B7 and Mathlib-leaf checks are vacuous; the duplicate and blueprint searches are recorded above.

- Step 1: checked the coefficient-datum, open-square, weakly-etale localization, sectionwise-limit, and quasi-compact-base-change statements; the restriction identifications and the induced quasi-compactness of (j') follow, with no hypothesis on (g). Verdict: pass.
- Step 2: checked the ringed-site adjunction/exactness, finite extension theorem, extension presheaf, scalar restriction, and module sheafification statements; the completed and finite coefficient actions are distinguished and the underlying sheaf comparison is explicit. Verdict: pass.
- Step 3: checked K-flat resolution, ringed-slice tensor, colimit, tensor-complex, K-flat, flatness, and coefficient-datum statements; the total-complex tensor comparison and every quotient transition are written. Verdict: pass.
- Step 4: checked the closed-subscheme existence, inverse-image, slice localization, ringed open-closed exact sequence, sectionwise limits, and immersion-limit statements; the kernel proof uses the required quasi-compact open and also covers the empty product. Verdict: pass.
- Step 5: checked exact countable products, derived products, levelwise tower abelianness, functorial Rlim, the strict-tower homotopy-limit, Roos-complex, Grothendieck, and enough-injectives statements; the signed fiber coordinates and chain homotopy are explicit. Verdict: pass.
- Step 6: checked intrinsic Koszul completion, tensor comparison, and completed-pullback reduction; the completion unit and both endpoint completeness claims are identified. Verdict: pass.
- Step 7: checked finite constant exact pullback, finite extension base change, site composition, inverse-image, completed-pullback, constant-completion equivalence, and resolving-class universal-pair statements; coefficient projection equations and quotient-transition compatibility are explicit, with no invertibility assumption on (c_g). Verdict: pass.
- Step 8: checked functorial Rlim and completed-pullback definitions against the strict tower comparison; both arrows are isomorphisms and the unit normalization is tracked through quotient augmentations. Verdict: pass.

I repaired `citations.json`: the citation for `lem-pur-left-derived-from-kflat-class` now contains that node's complete verbatim statement, matching the other 47 citations. A fresh check found 48/48 exact statement quotes and exact equality between `proof_deps` and the union of step uses. No node statement, dependency, proof step, source metadata, or Lean file was otherwise changed.
