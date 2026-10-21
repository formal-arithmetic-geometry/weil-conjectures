## Worker report

The delivery states `lem-pe-integral-completion-presentation` in
`Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation`. Its two theorem declarations
cover the two parts of the node. All new theorem proofs are `sorry`; all definitions
have explicit data. The item statement and proof are unchanged. The returned dependency-ownership repair is recorded below.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The coefficient extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; its valuation ring,
  chosen uniformizer and finite quotients are the existing Padic constructions.
- Any scheme is `(X : Scheme.{u})`, with no Noetherian, characteristic, boundedness
  or constructibility hypothesis. The site is exactly `Scheme.ProEt.topology X`.
- The pulled-back ring B and its internal modules are `AdicCompletion.ring` and
  `AdicCompletion.Modules`, from the recorded canonical-completion definition.
  The section-ring reconstruction is the existing `sectionModuleEquivalence`.
  The completed ring is `completedIntegralCommRingSheafUnrestricted.{u,u}`.
- `Encoding.ringIso` and `Encoding.functor_eq` express the coefficient identification
  and literal scalar relabelling along its inverse. `Encoding.derived` is the actual
  termwise derived equivalence. Encoding is a bundle of supplied data, with no choice
  or assertion of existence in its definition.
- `integral_completion_reduction_comparisons` supplies an integral encoding A and
  all positive finite encodings e. `SquareNormalized` pins the restriction squares
  on entire underlying abelian sheaves, after the recorded forward-functor equalities.
  Applied to the regular finite modules, this fixes the relation b_n = pi_n alpha;
  with the finite constant-function normalization it fixes the canonical integral-limit
  identification. Thus no arbitrary coefficient isomorphism is substituted.
- `FiniteComparison` is an isomorphism of functors with values in D(R_n), using the
  existing finite ordinary coefficient equivalence. The finite coefficient action is
  retained. `UnitCompatible` fixes its restriction on every actual reduction unit.
  The uniqueness clause fixes the derived comparison itself, by the tensor/restriction
  adjunction; it is the identity-pure-tensor comparison on K-flat representatives.
- The final equation of `integral_completion_reduction_comparisons` is exactly the
  quotient-transition square, after `restrictedComparison` restricts each finite
  comparison to the common completed integral derived category. Together with the
  unit equation this identifies the augmented tower, not merely its objects.
- K is an arbitrary object of `DerivedCategory (AdicCompletion.Modules l E X)`.
  The completeness hypothesis in `integral_completion_presentation` is exactly the
  recorded `AlgebraicGeometry.ProEtale.IsDerivedComplete`, including its specified
  zero-nullhomotopy Roos augmentation.
- Its first conclusion is `IsSfDerivedComplete` of the relabelled object. Unfolding
  that existing predicate gives a product witness and delta with
  `IsDerivedLimitTriangle (sfDerivedReductionTransition ...) Khat
  (Pi.lift (sfDerivedReductionUnit ...)) delta`. Thus the first arrow is the product
  of the actual reductions, rather than an unspecified lift to a derived limit.
- Its second conclusion quantifies over every `FiniteFieldDatum.{d}` and every
  `hl : l ≠ D.p`, and gives the existing `WeilConjectures.IsDerivedComplete`.
  This is precisely the global interpretation of the node. The earlier conclusion
  has no characteristic restriction. The normalization data in this theorem's
  binders are supplied for every l,E,X by the preceding existence theorem; they are
  the named canonical coefficient presentation in the informal statement, not an
  extra mathematical assumption on K.

Dependency interfaces read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, with the original coefficient constructions.
- Mathlib `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`, `SheafOfModules`,
  `DerivedCategory`, `HasDerivedCategory`, and exact-functor localization.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `coefficientRing`,
  `condensedRingObj`, and the strong monoidal inverse image from the point.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`,
  `sfb_integral_coefficient_limit`, including its finite-projection normalization.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`, `IsDerivedComplete`,
  `AdicCompletion.derivedReduction`, `restrict`, `integralStep`, and the actual
  tensor/restriction adjunctions in the internal-module API.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`,
  `scalarReductionDerivedExtension` and exact `scalarReductionDerivedRestriction`.
- `Sheaf.Paper.FiniteDiscreteOrdinaryEncoding`, the newly published
  `FiniteDiscreteOrdinary.Encoding`, `sectionEncoding`, and `ordinaryDerived`.
  This is the exact small owning module of the recorded normalized-encoding node.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
  `sectionRingSheaf`, `sectionModuleEquivalence`; and
  `Sheaf.CategoryTheory.InternalSectionTensorComparison` for the tensor/K-flat bridge.
- `Sheaf.Paper.SfIntegralReductionTower`, `sfDerivedReductionUnit`,
  `sfDerivedReductionTransition`; `Sheaf.Paper.SfDerivedComplete`,
  `IsSfDerivedComplete`; `Sheaf.Paper.SfDerivedCompleteLegacyComparison`,
  `sfDerivedComplete_iff_legacy`; and the recorded global branch of
  `Sheaf.Paper.DerivedCompleteOnSlices` through `DerivedCompleteUnrestricted`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
  `IsDerivedLimitTriangle`, including its fixed first map and sign convention.
  The recorded K-flat, derived-change-of-rings, exact-products, derived-limit,
  strict-Roos and tower-well-definedness modules are proof imports.

Edge cases checked: n=0 denotes exponent 1, so no positive level is omitted.
Zero K, the empty scheme, and arbitrary unbounded K are allowed. No hypothesis l != p
occurs before the global legacy interpretation. The product is existentially supplied
by the existing Roos predicate rather than assumed or replaced by an arbitrary product.
The site has object universe u+1 and arrow universe u; modules have universe u+1.
The internal derived category has morphism universe u+1 while the sectionwise standard
localization has morphism universe u+2. The termwise equivalence explicitly permits
these different localization sizes; no site-size equality is imposed.

Searches: msearch LeanFinder for preservation of derived completion under integral
coefficient identification returned ordinary adic-completion/perfectoid declarations,
not this statement. Loogle `"IsDerivedLimitTriangle"` and Mathlib grep
`IsDerivedComplete|[Rr]oos|integral.*completion` in Algebra/Homology returned zero hits.
LeanSearch for the coefficient-isomorphism/module-sheaf equivalence returned structure
sheaf and section lemmas, not the desired encoding or theorem. Loogle
`"SheafOfModules", "restrictScalars"` returned ordinary presheaf scalar-restriction
interfaces. The full raw search results are preserved in the new node's searches.
Project and upstream rg searches found no declaration for this unbounded two-presentation
comparison. `IntegralCriterionReductions` has a comparison of constructible predicates
with a Noetherian hypothesis, so is not an exact existing theorem for this node.

No statement correction or STATEMENT-DISPUTED flag is needed.

## New nodes

`def-pe-integral-presentation-encoding` packages a supplied ring-sheaf isomorphism and
an additive module equivalence whose forward functor is exactly the existing section
functor followed by restriction along its inverse. Its source is the isomorphism-of-rings
specialization of Stacks 06YY and the coefficient comparison in the blueprint's final
sentence. This is data packaging, not a second ring, module category, tensor product,
chosen comparison map or completeness definition. The specialized chosen functor in
`IntegralCriterionReductions` does not provide the general supplied-data bundle needed
here. Existing finite Encoding is reused verbatim for finite levels. Mathlib, upstream,
project, DAG and blueprint searches are recorded in the new node. The definition
asserts no existence; the item's normalized-comparison theorem supplies it.

The attempted use of the parent's chosen transport imported
`ProEtaleCoefficientComparisonsPullback` and its unrelated localization/constructibility
proof imports. scompile failed before this delivery at
`IntegralConstructibleSequentialHom.lean:114:16`, unknown `constructible_of_iso`.
The delivered version uses smaller existing interfaces, without modifying any library
source, creating an import cycle, or copying the parent's chosen transport.

`def-pe-finite-discrete-presentation-encoding` records the existing definitions in
`Sheaf.Paper.FiniteDiscreteOrdinaryEncoding`, with primary declaration
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.Encoding` and its concrete
coefficient, section-action, fixed-scalar and termwise-derived helpers. Its data
and normalization are copied by reference, not redefined. The source is Stacks Tags 00YV, 03CY and 015F: algebraic structures under
inverse image, module sheafification and termwise exact-functor localization.
These are the constructions named in the published encoding docstrings. Mathlib LeanSearch,
Loogle and grep found no exact encoding; project grep found this precise module;
DAG definition-node grep and blueprint_refs search found no definition-node owner.
The similarly named common-finite-discrete-encoding node binds a different
fixed-scalar equivalence. The new existing:true record supplies definition ownership
without asserting or choosing existence. Its statement lists the full structure:
ringIso and normalization on each constant scalar, ordinary and ordinary_functor,
fixed and fixed_functor, all four additive fields, and the two actual termwise
derived equivalences. It works for arbitrary commutative topological A as the
published structure does; the item uses its finite discrete specialization.

## Second reading by Q05

The dispatcher requires this worker to work alone; this is a separate second pass by
the same worker, not a claim of independent review. The maintainer supplies the
independent review of the delivery.

I reopened the node and both modules and checked the prime/extension/scheme binders,
positive indexing, finite actions, restriction normalizations, units and transitions,
and both completeness conclusions. In particular, an arbitrary natural isomorphism
would have been too weak: the delivered normalization is equality on whole abelian
sheaves, and the derived comparison is uniquely fixed by units. The transition square
uses the same restricted finite comparison. The Roos condition keeps the canonical
reduction units as its first map. There is no constructibility or boundedness binder.
The new structure's forward functor equality excludes unrelated equivalences, and its
derived equivalence is constructed termwise. No mathematical clause changed on this
reading. Routine compiler adjustments make the spectral quotient topology explicit at each finite
encoding projection, and install the already recorded exactness instances locally in
the body of `derivedSquare`. These change no mathematical hypotheses or constructions.
Preflight adjustments, if any, are recorded below.

## Validation

The prescribed scompile.py check passed for both delivered files against current
server sources: IntegralPresentationEncoding (8.8 s) and
IntegralCompletionPresentation (18.5 s), each with two threads, nice 19 and the
unchanged 60-second limit. No errors or warnings were emitted. The existing finite
encoding dependency was confirmed against the server and cached by the wrapper.

The prescribed `deliver2.py Q05 lem-pe-integral-completion-presentation --no-push`
passed preflight and per-file compilation: `OK (dry run)` at bda712fb73c. No
preflight repair was needed. The final delivery uses the same Lean files and node
records, with this validation entry added to the report.

## Returned delivery repair (L, immutable head 2a6d22f27666)

H2 is repaired by adding `def-pe-finite-discrete-presentation-encoding` as an
existing:true definition owner of the published finite Encoding data, replacing
`lem-sf-finite-discrete-normalized-encoding` in the item's `stmt_deps` with this
definition node. The theorem is now in `proof_deps` only: its `encoding_exists`
proves the existence used in the normalized-comparison proof, while the statement
takes encodings as supplied data and never calls `.choose`. The existing public
import already provides the data and the proof theorem. Neither Lean file changed.

I compared the retained packet with the current shared read clone before editing:
only `lean` and `stmt_deps` differed; the original statement and proof were intact.
The prescribed saved-packet dry run passed at `556c174c9df` after its automatic
retry against current server sources. I retained both Lean files byte for byte.
The dependency ownership repair requested by the return is the only new change;
the updated-packet validation is recorded below.

Second reading of the repair: I reopened the published Encoding fields and the
item's FiniteEncoding, SquareNormalized, derivedSquare and FiniteComparison.
The new node owns exactly the plain definitions used there, including
ordinary_functor and ordinaryDerived. It adds no existence premise and no
mathematical assumption to either theorem. The normalized coefficient squares,
unit uniqueness, transitions and both completeness conclusions are unchanged.
The edge cases n=0 (positive exponent 1), K=0, empty X, unbounded K and the
unrestricted-prime versus global l != p distinction remain as in the accepted
independent review. No statement correction or STATEMENT-DISPUTED is needed.

## Repair validation and tool failure

The required saved-packet dry run passed at `556c174c9df`. The repaired packet
adds the finite-encoding definition owner and moves the existence theorem to
proof_deps exactly as requested by L's H2 return. Its new definition-node citations
match its stmt_deps; all retained Lean lines meet the 100-character convention,
and both files explicitly disable autoImplicit. The standalone scompile retry
reported a server timeout on IntegralCompletionPresentation after compiling
IntegralPresentationEncoding in 34.4 s. The subsequent repaired-packet dry run
completed its compilation phase and reached preflight, which rejected only the
node-field change below.

The prescribed repaired-packet `deliver2.py --no-push` exited 1 with:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

Read-only diagnosis of tools/node_fields.py, check_statement_change, lines 85--93
confirms that adding statement_change while preserving the statement is rejected
too: “statement_change is new or changed but the statement is as on the base”.
This conflicts with the explicit return instruction to keep the theorem only as
a proof dependency: it was absent from proof_deps on the base, so the required
repair necessarily adds it. The reviewer accepted the mathematical statement.
No justified mathematical correction was found, and none has been invented to
bypass this gate. The launcher tools were not edited or copied. The repaired
packet is retained, with the original statement and both Lean modules unchanged.

I also audited the sole citer, det-prop-integral-criterion-reductions: its proof
step 5 uses the same reduction tower and completeness conclusion, both unchanged
by the repaired definition ownership. It continues to hold. No citer was edited.
No push occurred for this repair.


## Retained-packet retry (2026-10-21, 07:51 UTC)

Following the dispatcher's retry instruction, I inspected this retained report and
ran the saved packet through the prescribed `deliver2.py Q05
lem-pe-integral-completion-presentation --no-push`, without restarting the
statement construction. I compared its node with the current shared read clone:
only lean, the authorized added definition/landed statement dependencies, and the
reviewer-required added proof dependency differ. The mathematical statement and
proof remain verbatim. Both Lean files are retained unchanged.

The current wrapper explicitly permits dependency-only proof repairs for a
maintainer return (deliver2.py lines 133–140), but the server preflight still
rejects the resulting addition. This retry passed its compilation phase (including
confirmation against current server sources after a local overlay timeout), staged
the six intended paths, and exited 1 at server preflight with exactly:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

The required self-check reopened both delivered Lean modules and the published
FiniteDiscreteOrdinaryEncoding definitions. The new definition owner lists the
actual Encoding data and ordinaryDerived construction. The item cites
`def-pe-finite-discrete-presentation-encoding` in stmt_deps, excludes
`lem-sf-finite-discrete-normalized-encoding` from stmt_deps, and includes that
existence theorem in proof_deps only. Both files disable autoImplicit and have no
lines exceeding 100 characters; the node statements have single TeX backslashes.
The accepted normalized maps, units, transitions, completeness conclusions and
edge cases remain unchanged. No mathematical statement correction is justified.

The requested ownership repair is complete in the retained packet. Removing its
proof dependency would contradict the explicit return; inventing a changed
statement would contradict the accepted mathematical statement. No launcher or
project tool was edited or bypassed, no live source was modified, and nothing was
pushed. The remaining blocker is the server preflight's rejection of this
reviewer-required dependency-only repair.


## Retained-packet retry (2026-10-21, 07:54 UTC)

Inspected the saved report, then ran the saved packet first with the prescribed
`deliver2.py Q05 lem-pe-integral-completion-presentation --no-push`. Retained both
Lean modules and all three node records unchanged. The read-only comparison with
the current shared clone again found only lean, added statement dependencies and
the reviewer-required proof dependency; the mathematical statement and proof are
verbatim. No released repair-note file exists for this item.

The self-check reopened both delivered modules and the published finite Encoding
structure, sectionEncoding and ordinaryDerived. The existing:true definition owner
records precisely these supplied data and their termwise localization. The item
cites def-pe-finite-discrete-presentation-encoding in stmt_deps and cites
lem-sf-finite-discrete-normalized-encoding in proof_deps only. Neither theorem
chooses Encoding from encoding_exists. Both Lean files explicitly disable
autoImplicit, and neither has lines over 100 characters. The accepted clause and
edge-case analysis remains unchanged.

The dry run timed out in the local overlay on the published finite-encoding
dependency, performed its automatic confirmation against current server sources,
then staged the six intended paths and reached server preflight. At 07:54 UTC it
exited 1 with the same two concrete diagnostics:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

Read-only inspection again confirmed that deliver2.py explicitly permits the
maintainer-return dependency-only proof repair, whereas tools/node_fields.py
check_statement_change rejects it without a changed mathematical statement. The
reviewer specifically requires the theorem to remain only a proof dependency;
removing it would undo that repair. No mathematical defect justifying a statement
correction was found. The remaining failure is this tool mismatch. No launcher
or project tool was modified or bypassed; nothing was pushed.


## Retained-packet retry (2026-10-21, 07:59 UTC)

Inspected report.md and ran the saved packet first using the prescribed
`deliver2.py Q05 lem-pe-integral-completion-presentation --no-push`. The
wrapper retried against current server sources after a local overlay dependency
timeout, staged the six intended paths, and exited 1 at server preflight.
Nothing was pushed. The concrete remaining diagnostics are:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

The required self-check reopened both delivered Lean modules, the published
FiniteDiscreteOrdinary.Encoding structure and ordinaryDerived, and all three
packet node records. The new existing:true definition node owns the exact
published data, including ordinary_functor and the actual termwise derived
equivalence. The item cites that definition in stmt_deps and keeps
lem-sf-finite-discrete-normalized-encoding in proof_deps only, as L requires.
The supplied encodings are not obtained by choosing from encoding_exists.
Both modules disable autoImplicit, contain no lines over 100 characters, and
the JSON records retain indent 1, Unicode text and final newlines.

Compared with the current read clone, the packet changes only lean, added
statement dependencies, and the reviewer-required proof dependency; the
mathematical statement and proof remain verbatim. The sole citer is still
det-prop-integral-criterion-reductions, whose completeness comparison is unchanged.
No released repair note exists for the item. No new mathematical issue or
justification for changing its accepted statement was found.

Read-only inspection confirmed the mismatch: deliver2.py permits adding proof
dependencies for a maintainer return without changing the statement, while
tools/node_fields.py check_statement_change rejects that same change. Removing
the theorem would undo the explicit return instruction; inventing a mathematical
statement correction would not repair this tool failure. Both Lean files and
all three node records were retained unchanged. No project or launcher tool
was edited or bypassed, and no direct Git command was run.


## Retained-packet retry (2026-10-21, 08:02 UTC)

Inspected the saved report and ran the prescribed saved-packet dry run first.
Reopened both Lean modules and the published finite Encoding structure, its
ordinary_functor field and ordinaryDerived construction. The new definition
node owns those exact existing definitions; the consumer cites it in stmt_deps
and retains the normalized-encoding theorem only in proof_deps. No mathematical
statement, proof text or Lean file changed. The JSON comparison with the current
read clone confirms that the only proof_deps change is the reviewer-required
addition. Both modules explicitly disable autoImplicit and meet the line limit.
No released repair note exists. The sole citer remains
det-prop-integral-criterion-reductions, whose use is unaffected.

The wrapper retried against current server sources after the published dependency
compile timed out, then staged the six intended paths and reached server
preflight. It exited 1 with exactly the same two gate failures:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

Read-only inspection confirms deliver2.py explicitly permits this dependency-only
returned repair, whereas check_statement_change in tools/node_fields.py rejects
it. Removing the dependency would undo the explicit return instruction; no
mathematical statement correction is justified. The repaired packet is retained.
No launcher/project tool was edited or bypassed, no direct Git command was run,
and nothing was pushed.

## Dispatcher retry validation (2026-10-21)

As instructed, this retry first read the retained report and ran the saved packet
through deliver2.py --no-push before considering any edits. The retained H2
repair already owns the finite Encoding definitions with the new definition
node, cites that node in stmt_deps, and keeps encoding_exists only in proof_deps.
The current read clone still has the original statement and proof unchanged.
Both Lean files remain byte for byte as independently reviewed. JSON formatting,
verbatim signature records, explicit autoImplicit false, line widths and the
new definition nodes' exact statement-citation sets passed the self-check.
I reopened the published finite Encoding fields and its ordinaryDerived helper;
the new existing:true definition-owner record matches them exactly.

The launcher's deliver2.py now explicitly accepts additive proof_deps repairs
without a statement correction (read-only inspection of lines 133--140).
Nevertheless the prescribed dry run, after automatically retrying the local
overlay timeout against current server sources, reached server preflight and
again failed with exactly these two reasons:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

The tool reported base ed8eb9783 and nothing pushed. This is the same remaining
validator conflict as the earlier retry: the reviewer specifically requires the
proof dependency, and accepted the mathematical statement unchanged. No source-based
statement correction is justified, and a statement_change with an unchanged
statement is itself rejected by check_statement_change. No launcher or repository
tool was edited or copied. The complete repaired packet is retained.

The standalone prescribed scompile.py then passed for both delivered files
(exit 0), with no errors or warnings: IntegralPresentationEncoding 6.6 s and
IntegralCompletionPresentation 12.0 s in their final library-path compiles.
The exact existing finite Encoding overlay also passed in 44.5 s. No timeout
limit or compiler settings were increased. Only the server preflight conflict
above remains; nothing was pushed.


## Saved-packet retry (2026-10-21, 08:13 UTC)

Read the retained report and ran the required saved-packet dry run before any
edits. All three server compilation checks completed, and the wrapper staged
the six intended delivery paths. Server preflight exited 1 against base
9fbe13949 with these two diagnostics:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

The self-check reopened both retained Lean modules and the published finite
Encoding structure, ordinary_functor and ordinaryDerived. The new definition
owner records those exact supplied-data definitions. The item cites that owner
in stmt_deps and the existence theorem only in proof_deps, as the return requires.
Both modules disable autoImplicit, meet the 100-character line limit, and retain
the independently accepted statements. All three JSON files have canonical
indent-1 formatting and final newlines. Comparison with the current read clone
shows only lean, additive stmt_deps and the required additive proof_deps change;
statement and proof remain verbatim. No released repair note exists.

Read-only inspection of deliver2.py and tools/node_fields.py confirms the tool
mismatch: the wrapper permits additive proof dependency repairs without a
statement correction, while check_statement_change rejects them. No mathematical
statement correction is justified, and removing the proof dependency would undo
the reviewer's explicit instruction. No tool was modified or bypassed. The Lean
files and node records are retained unchanged; nothing was pushed.


## Retained-packet retry (2026-10-21, 08:17 UTC)

Inspected the retained report and ran the prescribed saved-packet dry run first.
The wrapper checked three Lean files on the server and reached server preflight;
no compilation failure was reported. The current run staged the six intended paths
and checked against base 083cf3357. It failed with exactly:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

The self-check compared the saved node with the current shared read clone and
reopened both delivered Lean modules and FiniteDiscreteOrdinaryEncoding. The only
changed item fields are lean, stmt_deps and proof_deps. The mathematical statement
and proof are verbatim. The finite-encoding definition owner records the published
Encoding structure, concrete section functor, ordinary_functor and ordinaryDerived;
the item cites this definition node in stmt_deps and the normalized-encoding
existence theorem only in proof_deps. The latter is the sole added proof dependency
and is explicitly required by return L/H2. Both Lean files disable autoImplicit
and have no lines over 100 characters. No released repair note is present.

The accepted normalization, units, transitions and completeness conclusions are
unchanged. This is a definition-ownership repair, not a mathematical statement
correction. The server gate still treats the required proof dependency addition
as a statement correction. Removing it would violate the return, while fabricating
a statement change would violate the stage-2 contract. No tool or live source was
edited or bypassed. The retained repair is complete; the tool refusal prevents
delivery, and nothing was pushed.

## Retained-packet retry (2026-10-21 08:28:17 UTC)

As required by the repair brief, I first inspected the retained report and ran
`deliver2.py Q05 lem-pe-integral-completion-presentation --no-push` on the saved
packet without changing it. The wrapper checked three Lean files on the server
and reached preflight. It again rejected exactly the required proof-dependency
addition, with the following diagnostic:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected'

A fresh parsed comparison with the current shared read clone confirms that the
statement and proof are identical. The only added proof dependency is
`lem-sf-finite-discrete-normalized-encoding`, required explicitly by the return.
The statement dependencies cite the new definition owner rather than that
theorem. I reread the published Encoding, ordinary_functor and ordinaryDerived
definitions and verified that the existing:true owner points to those exact
definitions. Read-only inspection of tools/node_fields.py confirms that adding
statement_change with an unchanged statement would also be rejected. Thus this
is the same tool-policy conflict, not a Lean or mathematical defect. No node or
Lean file was changed in this retry, no tool was patched or bypassed, and
nothing was pushed. The complete requested repair remains in the sandbox.

The delivery invocation (without --no-push) also stopped at the same two
preflight reasons and explicitly printed "PREFLIGHT FAILED, nothing pushed."

## Current repair retry (2026-10-21)

The required first action on the retained packet, `deliver2.py Q05
lem-pe-integral-completion-presentation --no-push`, again exited 1 before any
push. Its current server preflight reports the same two errors: `(b) statement
correction: the item changed in proof_deps without a statement correction` and
`(e) the item's statement is corrected but the report has no non-empty section
'## Statement corrected'`. The packet has no statement_change and its statement
and proof equal the shared base. The only added proof dependency is
lem-sf-finite-discrete-normalized-encoding, explicitly required by the H2 return.
Removing that dependency would undo the return instruction. The current
read-only tools/node_fields.py, check_statement_change, still rejects both a
proof_deps-only change and a new statement_change when statement is unchanged.
This is a tool refusal of the requested nonmathematical dependency repair; no
mathematical statement correction was invented and no launcher tool was changed.

Explicit scompile.py of both retained Lean files then exited 0 without warnings:
IntegralPresentationEncoding library check 6.6 s and
IntegralCompletionPresentation library check 12.0 s. The JSON layout, exact
recorded signatures, explicit autoImplicit false, 100-character Lean line limit,
and returned H2 dependency ownership were checked again successfully. The
existing finite Encoding structure was reopened and matches its new definition
owner, including ordinary_functor and ordinaryDerived. The Lean files and node
records are retained unchanged. Delivery remains blocked at the preflight gate;
no push was attempted.


## Saved-packet retry (2026-10-21 08:40:36 UTC)

Read the retained report and ran the prescribed saved-packet dry run before
considering changes. The wrapper completed its three server Lean checks and
staged the six intended paths. Server preflight exited 1 with exactly:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected'

The concrete output is retained in retry-dry-run.log in this sandbox. Nothing
was pushed. Reopened both delivered modules, the existing finite Encoding
structure, ordinary_functor and ordinaryDerived. The existing:true definition
owner matches these exact definitions. Parsed comparison with the current read
clone confirms the statement and proof are unchanged; the sole proof_deps
addition is lem-sf-finite-discrete-normalized-encoding, expressly required by
L/H2. That theorem is absent from stmt_deps, which cites the new definition
owner. Both nonexisting records contain verbatim source signatures, both Lean
files disable autoImplicit and satisfy the 100-character limit, and all JSON
files retain the required layout. The sole external citer remains
det-prop-integral-criterion-reductions; its use is unaffected. No repair note
exists for the item.

Read-only inspection again confirms that deliver2.py explicitly permits additive
proof-dependency repairs without statement correction, while
check_statement_change in tools/node_fields.py rejects them and also rejects a
new statement_change when the statement is unchanged. Removing the dependency
would undo the return; fabricating a mathematical correction would misrepresent
the accepted statement. This is an actual tool refusal, not an unresolved Lean
repair. No tool or live source was edited, copied or bypassed. The complete H2
repair and Lean files remain unchanged.


## Saved-packet repair verification (2026-10-21 08:42 UTC)

Ran the required saved-packet deliver2.py --no-push first. The wrapper checked
three Lean files on the server and staged the six intended paths, then failed
server preflight with two reasons:

> (b) statement correction: the item changed in proof_deps without a statement correction
> (e) the item's statement is corrected but the report has no non-empty section '## Statement corrected'

Fresh parsed comparison against the refreshed shared read clone confirms that
statement and proof are unchanged; the sole added proof dependency is
lem-sf-finite-discrete-normalized-encoding, expressly required by return L/H2.
The theorem is absent from stmt_deps, which cites the new definition owner.
Reopened the published Encoding, sectionEncoding and ordinaryDerived: the
existing:true record owns exactly those definitions. JSON formatting, explicit
autoImplicit false and the 100-character Lean line limit pass.

Read-only inspection of deliver2.py lines 133--140 confirms that the wrapper
permits this additive proof-dependency repair. tools/node_fields.py
check_statement_change still rejects it without a changed statement, and also
rejects a new statement_change when the statement is unchanged. No source-based
mathematical correction is warranted. Removing the proof dependency would
violate the return. This is a tool refusal of the completed dependency repair.
No tool or live source was edited or bypassed; no Lean or node change was needed,
and nothing was pushed.


## Successful retained-packet verification (2026-10-21)

The prescribed first saved-packet dry run now passes: `OK (dry run): commit
570a199e9a6 passes the preflight and compiles; nothing pushed`. The current
base includes the normalized finite-encoding existence theorem in proof_deps
and its use in the first proof step, resolving the earlier gate conflict.
Rebased the sandbox proof field to that current base; this is retained upstream
metadata, not a statement correction. Both delivered Lean files remain unchanged.

Reopened both modules and the published FiniteDiscreteOrdinary.Encoding,
sectionEncoding and ordinaryDerived definitions. The new existing:true definition
node owns exactly the supplied finite encoding data and termwise derived helpers.
The item cites that definition node in stmt_deps, and the existence theorem only
in proof_deps. No .choose or new existence assumption occurs in its definitions.
The normalized squares, unit uniqueness, quotient transitions and fixed-first-map
Roos conclusion retain every clause accepted in L's independent review. The
global l != p form is unchanged, and positive indexing, zero K, empty schemes
and unbounded complexes remain allowed. Both Lean files disable autoImplicit,
all lines are at most 100 characters, all JSON files use the required layout,
and the item's mathematical statement is identical to the current base.
No statement_change is warranted. The earlier blocked entries above are
superseded by this successful server preflight and compilation.
