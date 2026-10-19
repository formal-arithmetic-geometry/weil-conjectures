## Worker report

The module `Sheaf.Paper.AdmissibleVerdierExchange` states
`WeilConjectures.AdmissibleVerdierExchange.verdier_exchange` with one `sorry`.
All other declarations contain real definitions or construction records. The item
statement, proof, and proof dependencies are unchanged. The new definition node `def-sf-verdier-exchange-data` records the reused
exchange constructions by `existing: true`; the already-landed
`lem-weil-structure-direct-images-constructible` records the coefficient prime unit.
No dependency module or new Lean construction is introduced.

I read the node, its two statement dependencies and recorded declarations, the
current main-20261015 sk-thm-sf-package/fix-cor-verdier-exchange statement and proof,
and the five-step split proof in the DAG. The resolved stage-1 repair note says to
keep the statement unchanged; this delivery does so.

Hypothesis and clause correspondence:

- The global finite-field datum is `D : FiniteFieldDatum.{u}`. Its coefficient
  datum `C : D.CoefficientDatum` includes the prime and `C.different`. The finite
  extension, positive exponent, and operation datum are `E`, `n`, `hn`, `_S`.
  Scheme universes, coefficient universes and stage categories agree with the
  existing operation datum; there is no added equality of site universes.
- Finite-type k-schemes are `X`, `Y`, their `Over (Spec (.of D.k))` instances,
  `LocallyOfFiniteType` and `QuasiCompact` structure-map instances. Separatedness
  of their structure maps is necessary for the explicitly assumed admissibility
  and its compactifications. The morphism has `IsOver`, `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` instances.
- `atStage` is case analysis on the EXISTING `Stage`: finite E n (n : ℕ+),
  integral E, rational E, or closed. Each branch invokes exactly the recorded
  corresponding `IsExceptionalAdjointAdmissibleAt...` predicate. It does not
  replace FullCD by constructible cohomological dimension or assume the warning's
  false ambient statement. `baseUnit` maps `finiteFieldDatumPrimeUnit` through
  the explicit germ/global-sections ring homomorphism. No invertibility
  hypothesis is added; the local defProp style-linter exception allows this
  explicit proof term to remain a definition rather than a stage-2 proved theorem.
- `admissible ... s` is precisely the conjunction for f, a_Y and a_X=f;a_Y at
  that coefficient stage. It fixes the base-over-base structure to the identity.
  The equality with the given a_X follows from f.IsOver. Compactifications are
  universally quantified presentations of the compactification-independent
  operations, not extra geometric restrictions.
- The coefficient unit and dualizing objects reuse `VerdierExchange.StageData`,
  `RingRealization`, and their `unitIso`; the latter identifies the unit with the
  actual coefficient sheaf in degree zero. The duals `StageData.dualX/dualY`
  are the actual recorded internal Hom into B.G(unit) and A.G(unit).
  The operation datum argument is construction data for these same operations;
  the universally quantified `System`s are normalized realizations, not arbitrary
  replacements or additional existence assumptions.
- M ranges over every object of the EXISTING coefficient category
  `ConstructibleExceptionalCoefficients.C`. Finite/integral stages are exactly
  the finite-Tor full subcategories; field stages impose no extra Tor restriction.
  `Package.conclusion s hs` is asserted for each selected admissible stage,
  without assuming admissibility at unrelated coefficient stages.
- The isomorphism is `StageConclusion.epsilon`, in the exact requested direction
  F.op;D_Y to D_X;Rf_*. Its component equation identifies it with
  `StageData.epsilon`, the actual projection/evaluation/adjunction transpose;
  an arbitrary objectwise isomorphism or arbitrary map cannot satisfy this field.
- Naturality is contained in that natural isomorphism. `exchangeNaturality`
  retains the published coefficient square for each projection-compatible
  comparison and structure-mate equation.
- Finite quotient maps, integral reductions, and ramified scalar extensions are
  `ringScalar` with `Allowed`, the published scalar functors, normalized support
  comparisons, and `ScalarConclusion.exchange`. `integralAlpha_normalized`
  pins the integral structure mate to the recorded proper/open compositor.
  `rationalization`, `rationalScalar`, and `common` retain the corresponding
  coefficient comparisons and their exchange equations. The two endpoint
  admissibility proofs restrict only the domain of each compatibility assertion.
- Shifts are `StageConclusion.shift`, `ringShifts`, and `ScalarShifts`.
  `RingShiftRealization` fixes them by the signed Hom-complex model, rather than
  choosing rescaled shift comparisons; on opposite categories this is [-r].

Dependencies used (module and declarations):

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`; read its
  finite/integral/rational/common-stage Verdier definitions and underlying stages.
- `Sheaf.Paper.ExceptionalAdjointAdmissibility`: the four exact
  `IsExceptionalAdjointAdmissibleAt...` predicates and their finite-system
  reduction/scalar requirements. Their signature's base invertibility argument
  is supplied by the explicit `baseUnit` construction.
- `Sheaf.Paper.VerdierExchange`: `StageData`, its duals and canonical `epsilon`,
  `StageConclusion`, `RingRealization`, `RingProjection`, `RingShiftRealization`,
  `StageScalar`, `ScalarConclusion`, `ScalarShifts`, `composition`,
  `integralAlphaRealization`. This is an already-landed realization interface,
  recorded by the new definition node `def-sf-verdier-exchange-data`, which is
  cited in stmt_deps. The exchange theorem is not a statement dependency.
- `Sheaf.Paper.DirectImagesConstructible`: `finiteFieldDatumPrimeUnit`, recorded
  by lem-weil-structure-direct-images-constructible, added to stmt_deps.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` (also recorded
  by def-weil-exceptional-inverse-image): existing `Stage`, `C`, `System`,
  coefficient/scalar/field operations. Imported through VerdierExchange.
- Proof imports: `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`
  (fix-prop-adjunctions), `Sheaf.Paper.BasicOperationsCoefficientReduction`
  (lem-fix-operation-reduction), and
  `Sheaf.Paper.CanonicalOriginCompactSupportComposition` (thm-sf-comp-composition).
  fix-lem-tensor-adjunction has no recorded module, so has no additional import;
  the docstring keeps its precise proof role. Nothing waits on it.

Searches:

- msearch leanfinder, “Verdier duality exchanges compact support direct image
  with direct image natural coefficient reduction shifts”: 8 hits, generic sheaf
  pushforward composition/compatibility, no exact theorem.
- msearch loogle, “CategoryTheory.Adjunction, CategoryTheory.NatIso”: 0 hits,
  unknown identifier CategoryTheory.NatIso.
- msearch grep, “Verdier|verdierDual|rightDerivedLowerShriek”, CategoryTheory:
  19 generic references to Verdier/triangulated/localization infrastructure.
- rg in WeilConjectures for the node ID and Verdier/exchange terms located
  Etale.Derived.TensorHom.nonempty_iso_verdierDual_rightDerivedLowerShriek.
  I opened its complete signature and docstring: only finite etale coefficients
  and objectwise Nonempty, no coefficient or shift assertion, so not an exact match.
- rg in Sheaf for the same terms located the all-stage `VerdierExchange` module.
  Its theorem has no admissibility assumptions, so recording it as an exact
  existing match would drop the node's hypotheses. Instead its canonical maps
  and exact comparison/shift interfaces are reused in a conditional conclusion.
- Source search for `finiteFieldDatumPrimeUnit` located its existing theorem;
  no second coefficient-invertibility theorem is introduced.
- Traversing stmt_deps and proof_deps confirmed neither added dependency reaches
  this item: these added edges do not create a dependency cycle.

Edge cases checked from the definitions: identity f gives the identity-adjunction
exchange; M=0 and empty X give zero objects on both sides. Y=Spec k is the global
duality specialization. Every positive quotient is included, including n=1;
n=0 is excluded exactly by the original coefficient convention. All integer
shifts, negative as well as positive, are included. Scalar identity maps and
identity common-stage inclusions are included by the existing scalar interfaces;
nonflat finite quotient maps use the specified comparisons, not an invented
unrestricted base-change isomorphism. An elliptic structure map is not silently
assumed admissible. There is no statement dispute or source correction.

Validation: scompile.py only, against the published live library. The first compile
identified a defProp style warning in the explicit base-unit construction; it is
now scoped to that definition. The fully inlined equivalent proof was too expensive
to elaborate and was replaced by its shared explicit definition. No timeout limit
was changed. Final compile and delivery preflight results are recorded below.


## New nodes

`def-sf-verdier-exchange-data` owns the existing canonical constructions in
`Sheaf.Paper.VerdierExchange`, with `existing: true` and no delivered Lean module.
Its primary declaration is `WeilConjectures.VerdierExchange.StageData`;
`lean.statement` is its exact multiline signature from the published file.
The 33 explicit declarations from `composition` through `integralAlphaRealization`
are listed, including the ring-unit restriction auxiliaries, signed-shift models,
projection models, and scalar-mate definitions. The definition introduces
construction records and their compatibility predicates; it does not assert
existence of the exchange isomorphism or cite the exchange theorem.
Its two statement dependencies supply the existing six-functor operations and
the actual constructible stage/adjunction/scalar interfaces.

Source correspondence: proof step 1 supplies `composition` and the normalized
integral compositor; step 2 supplies the dualizing objects, duals and canonical
`StageData.epsilon`; step 3 supplies naturality, the two scalar squares and shifts.
`StageConclusion` requires a natural isomorphism with precisely these components;
`RingRealization` retains the coefficient unit, tensor/Hom/evaluation and ordinary
adjunction realizations; `RingProjection` fixes the actual proper/open projection;
`RingShiftRealization` fixes the signed Hom model. `StageScalar` and its five
auxiliary maps give the normalized coefficient arrows, and `ScalarConclusion`
and `ScalarShifts` state the square and shift predicates, without asserting them.
Thus the definition has real data and predicates and contains no postponed proof.

The DAG search for those qualified declarations found references only in theorem
records, and a scan of every definition node found no owner of this interface.
The project source search found its unique definition in the published module;
no copy is written. `blueprint_refs.py ancestor` identifies the item itself;
searches for `Verdier`, `exchange data` and `Verdier exchange realization` found
the related exchange statements but no blueprint definition of this interface.
The new node's `mathlib_searches` records the actual msearch LeanSearch,
LeanFinder and Mathlib grep results. LeanSearch returned generic shifted-Hom
declarations, LeanFinder returned rigid tensor-Hom and Tor declarations, and grep
found no stage/scalar realization interface. These do not replace the published
project constructions. Edge cases remain those checked above; the new node only
names those same constructions, with no additional geometric assumptions.

## Returned-delivery repair

H2 at immutable head `2f2560c1e463`: added the definition node above and replaced
`sk-thm-sf-verdier-exchange` in the item's statement dependencies with it.
The dependency on `lem-weil-structure-direct-images-constructible` is retained:
`finiteFieldDatumPrimeUnit` supplies exactly its own `IsUnit` conclusion.
The item's statement, proof, proof dependencies and Lean module are unchanged.
The `_S` argument is retained in the previously accepted signature, as advised.

Validation before repair: the retained packet passed `deliver2.py --no-push`
at generated commit `b15df819a6`, with the server compile and preflight both clean.
This mechanical pass did not address the independent H2 finding; the definition
node and dependency replacement above are the substantive repair.

Repaired-packet compile: `scompile.py NN fix-cor-verdier-exchange` on
`lean/Sheaf/Paper/AdmissibleVerdierExchange.lean` exited 0. Both server checks
were clean: sandbox `Sheaf.Stage2.Sandbox0` in 7.2 s and library-name compile
`Sheaf.Paper.AdmissibleVerdierExchange` in 7.5 s, with no warnings.
The new definition node reuses a published module; delivery preflight additionally
checks all 33 existing declaration names with a private server probe.
Self-check: only `lean` and `stmt_deps` differ in the item relative to the current
read clone. Both added dependencies were traversed through statement and proof
edges; neither reaches the item. The Lean file is unchanged (SHA256
`291e865f20f778b3d1a4783d1b6a65187bf40175bbd014d2cbb2ed505200908a`).


## Resumed validation (2026-10-19)

The retained packet already contains the substantive H2 repair. Rechecked the
new definition record against the published VerdierExchange source: its
StageData signature is verbatim, and its 33 recorded declarations and auxiliaries
are present. The item differs from the read-clone node only in lean and
stmt_deps. Both JSON files retain indent 1, ensure_ascii false and a final newline.
The delivered Lean file retains the SHA256 recorded above.

The required initial deliver2.py NN fix-cor-verdier-exchange --no-push failed
before building or pushing a commit. A second dry run reproduced the same failure
in the tool-generated existing-definition probe, preliminary Sheaf.Stage2.Check:

    error: import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit failed,
    environment already contains
    'AlgebraicGeometry.Scheme.etaleModuleCohomology_isColimit_of_isFiltered'
    from WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit

Separately, scompile.py on the delivered AdmissibleVerdierExchange module exited
0: sandbox check 10.4 s, library-name check 7.7 s, no warnings. A fresh sandbox
probe importing only the required existing Sheaf.Paper.VerdierExchange module
and checking StageData reproduced the duplicate-declaration error in 15.3 s.
An import-order repair probe importing SixFunctorOperationDatum and
ExceptionalAdjointAdmissibility before VerdierExchange timed out at the unchanged
60 s limit; the wrapper's current-source server confirmation also timed out.
Scratch probes are outside the delivery's lean directory.

The failing generated probe imports only the module mandated by the return's
existing:true record. Changing this item's imports cannot change that generated
probe. The required record remains existing:true on Sheaf.Paper.VerdierExchange;
no published source, launcher script, or delivery gate was edited. The current
published import closure and generated-probe failure prevent the prescribed dry
run from succeeding. No delivery was pushed in this resumed turn.


## Probe-mode diagnosis after the interrupted retry (2026-10-19)

Resumed the saved packet without changing its statement or Lean module. Checked
for a running item-specific delivery before the initial retry; none remained.
Two dry runs in this continuation returned exit 1 before any commit or push.
The second complete diagnostic is retained in scratchpad/delivery-dry-run.log:
the preliminary item check succeeds (6.7 s), but the generated existing-definition
probe fails at 1:0 importing VerdierExchange, in 3.3 s, with the same duplicate
etaleModuleCohomology_isColimit_of_isFiltered declaration recorded above.

The actual generated probe text in the prescribed deliver2.py starts with
`import Sheaf.Paper.VerdierExchange`, without a `module` header. In contrast,
the project source and this delivery are module-system files. A sandbox probe
with `module`, `public import Sheaf.Paper.VerdierExchange`, and the StageData
check passes both server checks, in 7.5 s and 5.8 s, with no warnings (full
output in scratchpad/module-probe.log). The original legacy-mode import fails
before it elaborates a declaration. This is a concrete generated-probe defect,
separate from the earlier timeout; no launcher tool was modified or patched.

Additional diagnostics do not establish a completed fresh verification:
a module-mode probe checking all 33 declarations completes its sandbox pass,
but its library pass times out; a fresh copy of the item also times out.
A scratch-only trial adding no_expose to baseUnit does not cure the timeout.
A marker at the first command after imports never appears in either the
sandbox attempt or server confirmation of that trial; the current trace
therefore does not implicate the baseUnit body. A private-import-only
module-mode probe also times out. These timeouts are recorded, not treated as
a successful compile or used to justify weakening any definition. The scratch
trials are outside lean/, are not delivered, and do not alter the saved item.

Self-check reconfirms both JSON layouts, the two exact recorded signatures,
and SHA256 291e865f20f778b3d1a4783d1b6a65187bf40175bbd014d2cbb2ed505200908a
of the unchanged delivered Lean file. Reading the current server source through
scompile.py --source confirms that the definition node names the published
VerdierExchange declarations. Only lean and stmt_deps differ from the current
read-clone item; its statement and proof remain unchanged. No delivery was
pushed. The generated legacy probe must be repaired by the launcher owner:
this worker is expressly forbidden to edit or privately patch launcher files.


## Current repair verification (2026-10-19)

Following the dispatcher instruction, inspected the retained report and ran the
required dry run before changing anything. The preliminary item compile passed
(37.3 s); the generated existing-definition probe failed at its first import
(12.2 s), with the duplicate declaration recorded below. The substantive H2
repair is retained: the new existing:true definition node owns all 33 plain
constructions, and the item cites it instead of the exchange theorem. No
statement, theorem signature, or canonical definition has been weakened.

Rechecked the record signatures verbatim against their source files, both JSON
layouts (indent 1, ensure_ascii false, final newline), and the unchanged item
module SHA256 291e865f20f778b3d1a4783d1b6a65187bf40175bbd014d2cbb2ed505200908a.
Only lean and stmt_deps differ in the item relative to the current read clone.
The definition node remains existing:true on Sheaf.Paper.VerdierExchange, as
the immutable-head review explicitly requires.

Fresh scompile.py diagnostic results, under the unchanged 60 s limit:

- The delivered item passes its preliminary check again (37.3 s).
- A module-mode probe importing only Sheaf.Paper.VerdierExchange and checking
  every one of the 33 recorded declarations passes both the sandbox and the
  library-name checks, each in 5.7 s, exit 0, no warnings. See
  scratchpad/resumed-module-checks.log and
  scratchpad/lean/Sheaf/Stage2/ModuleChecks.lean.
- A probe containing just the single line
  `import Sheaf.Paper.VerdierExchange` fails at 1:0 in 5.4 s. It has no
  definitions, theorem statements, or elaborated commands to optimize. See
  scratchpad/resumed-compile.log and
  scratchpad/lean/Sheaf/Stage2/LegacyImport.lean.

The exact failure is:

    error: import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit failed,
    environment already contains
    'AlgebraicGeometry.Scheme.etaleModuleCohomology_isColimit_of_isFiltered'
    from WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit

Read-only inspection of deliver2.py lines 71--87 confirms that it generates the
existing-definition check with legacy `import` commands and no `module` header.
The single-import counterexample reproduces exactly that generated format;
the module-mode probe verifies exactly the required declarations. This failure
is an import-environment rejection, not a timeout or expensive definition.
Changing baseUnit or adding no_expose in the delivered item cannot affect a
probe whose sole import is the separately published VerdierExchange module.
Changing the required definition record to omit or substitute its module would
violate the explicit H2 return. No launcher tool or published source was edited,
and no private tool copy or check bypass was used.

Final required dry run after the report update: deliver2.py --no-push exits 1
with the same preliminary Sheaf.Stage2.Check import rejection. Full output is
in scratchpad/resumed-final-dry-run.log. No commit was delivered or pushed.


## Interrupted-turn continuation verification (2026-10-19)

Checked the saved report, completed logs, and item-specific process list before
repeating a delivery. No interrupted delivery process remained. The required
initial `deliver2.py NN fix-cor-verdier-exchange --no-push` completed with exit 1,
before commit creation or push; its complete output is in
`scratchpad/continued-dry-run.log`. The preliminary item compile passed in
9.8 seconds. The generated existing-definition check failed in 4.3 seconds at
line 1, importing Sheaf.Paper.VerdierExchange, with the same duplicate
AlgebraicGeometry.Scheme.etaleModuleCohomology_isColimit_of_isFiltered error
recorded above.

A fresh `scompile.py` run of the retained module-mode probe checking all 33
recorded declarations passed both checks in 3.6 and 3.5 seconds, exit 0 and no
warnings (`scratchpad/continued-module-probe.log`). Read-only inspection of
deliver2.py lines 71--87 reconfirmed that its generated probe has legacy imports
and no module header. The module-mode probe changes only that header compared
with the generated import/check mode; the required existing:true definition
record remains on Sheaf.Paper.VerdierExchange. Changing the item's imports
cannot change this separate generated probe. No launcher script was edited,
copied, patched or bypassed.

A separate direct item scompile.py run subsequently timed out at 60 seconds in
both its local attempt and its current-source server confirmation; this is not
reported as a successful new compile (`scratchpad/continued-item-compile.log`).
The successful preliminary item compile above and the independently successful
all-declaration probe are reported separately from this variable timing result.

Self-check reconfirmed that only lean and stmt_deps differ in the item relative
to the current read clone; both JSON files retain indent 1, ensure_ascii false
and final newline; the item and definition signatures are verbatim in their
recorded sources; and the delivered Lean SHA256 remains
291e865f20f778b3d1a4783d1b6a65187bf40175bbd014d2cbb2ed505200908a.
The substantive H2 repair is retained unchanged. No delivery was pushed.
The generated legacy-import probe is a reproducible launcher-tool failure that
this worker is expressly forbidden to repair by editing the tool.


## Final resumed preflight repair (2026-10-19)

The launcher owner has repaired the generated existing-declaration probe to use
a module header. The fresh prescribed dry run completed both Lean checks without
errors or warnings and reached server preflight. Its sole failure was the new
definition node's blueprint.from.via: the current blueprint item is itself the
ancestor, so preflight requires the empty list. Changed only that new-node field
from [fix-cor-verdier-exchange] to []; no Lean file or mathematical statement
changed. The retained substantive H2 repair and all 33 existing constructions
remain intact. The landed direct-images dependency is retained as explicitly
approved in the independent review; the current preflight reports it only as an
advisory. Validation output is saved in scratchpad/oct20-dry-run.log.

Final repaired dry run: deliver2.py --no-push exited 0 and reported
"OK (dry run): commit 7bb5b945fa passes the preflight and compiles; nothing pushed"
(scratchpad/oct20-repaired-dry-run.log). This includes the delivered module and
the generated probe checking the existing definition declarations. Self-check
confirmed the exact recorded signatures against both source files, both JSON
layouts, only lean/stmt_deps changed in the item, and the unchanged Lean SHA256
recorded above.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
