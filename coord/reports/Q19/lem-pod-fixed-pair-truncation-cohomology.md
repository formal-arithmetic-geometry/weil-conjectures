## Worker report

Completed the retained draft as `Sheaf.Paper.FixedPairTruncationCohomology`. The delivery contains one unchanged module and two node records. The natural-language statement is unchanged. All four postponed theorems belong to lem-pod-fixed-pair-truncation-cohomology, with its source and full proof plans in their docstrings; every helper definition has real data. The repair adds a definition owner for existing comparison data. There are no dependency-module replacements or mathematical statement corrections.

### Matching hypotheses

- `D : FiniteFieldDatum.{u}` retains p prime, a≥1, q=p^a, the finite field of cardinality q, and its arbitrary chosen algebraic closure. `l`, `[Fact l.Prime]`, `hl : l ≠ D.p` retain the distinct coefficient prime.
- `Y₀ : Over (Spec (.of D.k₀))`, `[LocallyOfFiniteType Y₀.hom]`, `[QuasiCompact Y₀.hom]` mean precisely a finite-type k₀-scheme W₀. Its geometric fibre is literally `(D.geometricFiber Y₀).left`; its geometric Frobenius is `(D.geometricFrobenius Y₀).hom`. No separatedness of W₀ is imposed.
- `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]` retain every finite coefficient field. The theorem is invariant under its specified embedding in the fixed closure; the pullback and rational category themselves do not use the embedding. The common-stage assertion uses arbitrary `Ω : Type v` with `[IsAlgClosure (Padic l) Ω]` and every `Index l Ω`, using the existing `Coefficient.{u}` size transport. Thus no equality of scheme and coefficient-closure universes is imposed on truncations.
- `sfWeilFrobeniusPullback` and `sfCommonStageWeilFrobeniusPullback` are exactly the recorded P_W=Lg_W*. Their `IsoAlgebra` categories are exactly the recorded Weil pairs; the arrow equation is built into their inherited morphism type.
- The standard t-structures are the existing `sfRationalStandardTStructure` and `sfCommonStageStandardTStructure`, merely named by `fixedPairRationalTStructure` and `fixedPairCommonStageTStructure`. Geometric finite type is supplied by the existing `sfModelGeometricFinite` and `sfModelGeometricQuasiCompact`, not assumed anew.
- Point assertions use the source's coefficient size convention `Ω' : Type u`, exactly as the recorded point-fibre and point-transport interfaces. This is only the common-stage point clause, whose recorded dependency already has that convention; the scheme/common-stage truncation theorem retains the independent v.

### Matching conclusions

`fixedPairRationalTruncationCohomology` and `fixedPairCommonTruncationCohomology` assert `FixedPairTruncationCohomologySpec` on the two actual categories.

1. Its `cLE`, `cGE` are natural isomorphisms `tau ⋙ P ≅ P ⋙ tau`. The first conjunction is exactly the counit and unit characterizations in the node, written in Lean's left-to-right composition order. These characterize the canonical comparisons, rather than arbitrary commuting isomorphisms.
2. `IsoAlgebra.mapOfNatIso (cLE m)` and `(cGE m)` are the actual lifted functors. Reading the existing declaration gives the object structure `c.app K ≪≫ tau.mapIso K.str` and the underlying arrow `tau.map f.hom.f`, exactly tau(theta_K)c_K and tau(u). Its identities and compositions are the existing functor laws. The two displayed functor equalities with `IsoAlgebra.forget P` recover both underlying truncation functors.
3. The next conjunction gives the Weil-arrow equations for `t.truncLEι m`, `t.truncGEπ m`, and `t.truncGEδLE m (m+1) rfl`. The last equation includes `P.commShiftIso 1` and shift of the induced upper-truncation structure. These are all three arrows of `t.triangleLEGE m (m+1) rfl`; that is the existing standard distinguished triangle in the underlying category, with its existing distinguishedness theorem. Instantiating K by already truncated pairs also includes the successive standard truncation triangles through their canonical absorption identifications. No category-of-pairs triangulation is introduced.
4. The cohomology functor H is explicitly the composite of the lifted upper truncation, lower truncation, and i-shift. Its equality after forgetting is exactly `constructibleTruncationCohomology t i`, and `t.heart (H.obj K).carrier` says its values are degree-zero cohomology sheaves. Since H is a functor to the SAME fixed-pair category, every morphism it sends is equivariant. Its arrow action is the underlying composite cohomology map, by the existing mapOfNatIso arrow formula.
5. The shifted structures are specified, not assumed arbitrarily. `FixedPairRationalShiftNormalization` requires the coordinate-normalized and descent-normalized `IntegralCompletedComparison.Comparison` of the existing integral pullback. Its derived shift is restricted through the actual full-subcategory inclusion with its shift comparison, and rationalized through the natural comparison whose component is exactly the prescribed rational pullback object equality. `NatTrans.CommShift` fixes the rational shift square in every degree. `FixedPairCommonShiftNormalization` requires the square with every existing finite-stage inclusion; the comparison's inverse component is exactly the prescribed common-stage pullback object equality. The displayed equation expands shift compatibility of that comparison in all integer degrees. This uses the already existing signed Roos construction directly.
6. `fixedPairRationalPointPullback` and `fixedPairCommonPointPullback` are the actual recorded pullbacks on Spec k. Their transport definitions are the existing `frobeniusPointTransportRational` and `frobeniusPointTransportQbar`, inserting only the recorded object-identification maps. `fixedPair*PointFrobenius` is iota followed by Fib(theta), exactly F_A in categorical composition order.
7. `fixedPairRationalPointCohomology` and `fixedPairCommonPointCohomology` state both equalities of the node's three-term chain, and then the equation after every H^i. They quantify over every pair of resulting point complexes and every Weil morphism. Thus they apply to either supplied ordinary or compact-support direct-image lift wherever it exists; they require neither a further preservation theorem nor a new compactification or direct-image hypothesis. At E the functor is `DerivedCategory.coefficientFdCohomology`, the restriction of ordinary derived homology. At the closure it is `DerivedCategory.coefficientQbarCohomology`, the existing common-stage H^i(-) tensor Ω, including arbitrary common-stage representatives.

### Dependencies read and used

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber` (through the public fixed-pair import).
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`, `rationalDerivedPullback`, its object-normalized existence/uniqueness theorem, `commonStageDerivedPullback` and its object-normalized existence/uniqueness theorem.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilPrimeInvertible`, `sfWeilFrobeniusPullback`, `sfCommonStageWeilFrobeniusPullback`; `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`: `IsoAlgebra`, `forget`, `mapOfNatIso`, including its object/arrow formulas.
- `Sheaf.Paper.ConstructibleTruncations`: `constructibleTruncationCohomology`, `ConstructibleTruncations`, `constructibleTruncations_exists`.
- `Sheaf.Paper.SfConstructibleHeart`: the uniquely specified two standard t-structures; its owning node `def-weil-constructible-heart` is added to stmt_deps because its declarations are explicitly named.
- `Sheaf.Paper.SfCommonStageWeilCohomology`: the existing geometric-fibre finite-type/quasi-compact instances; this is already owned by the cited cohomology-sheaves notion. Its cohomology pair alone does not state the full item.
- `Sheaf.Paper.IntegralPullbackCompletedComparison`: `IntegralCompletedComparison.Comparison`, including `chainShift_coordinates` and `derivedShift_descent`. The new definition node `def-pod-integral-completed-comparison-data` owns this existing type, its shift predicates and field helpers. It replaces the theorem in stmt_deps; `lem-a1-integral-pullback-completed-comparison` is retained in proof_deps only.
- `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`: `texact_truncation_comparison`; `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology` and its imported ShortExact module supply uniqueness of truncation triangles and their canonical maps. These are proof imports.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: the actual point transport and point pullback object conventions; `Sheaf.SixFunctors.FrobeniusPointTransportNatural`: the recorded object equalities and `frobeniusPointTransport_natural`.
- `Sheaf.Paper.CoefficientCohomologyModules`: `coefficientFdCohomology`, `coefficientQbarCohomology`; Mathlib's `DerivedCategory.homologyFunctor` is retained through their definitions.
- `Sheaf.Paper.SfDerivedDirectImage` and `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` are imports of the two direct-image dependencies, read in full at their declarations. The point assertion is deliberately formulated for the supplied point Weil pairs as the node says, so it does not assert constructibility on a larger direct-image domain.
- The collector `def-weil-scheme-morphism-properties` defines no separate declaration; finite type uses the recorded Mathlib classes. The proof dependency `lem-pod-semilinear-field-operation-lifts` has no Lean record on the current base, so it has no module to import. Its proof role is described in the theorem docstrings; the delivery does not try to prove or replace it.

### Edge cases and searches

Checked the statement on the zero object, a single-degree object at either side of each cutoff, i=0, negative degrees/shifts, the empty scheme, and non-separated finite-type W₀. No hypothesis excludes these. The shifted boundary retains the signed shift comparison, including odd and negative shifts. Common-stage arrows need not be represented over the original fields: the functor and all point equations quantify over the actual quotient-category Hom types. Identity scalar extensions and further extensions remain included. The point claims only use the given Weil-arrow equation, so neither additional direct-image existence nor separatedness can enter their proof.

Searches use the prescribed msearch.py wrapper. The retained searches.jsonl also records the earlier attempt.

- LeanFinder, `Truncations and cohomology of Frobenius fixed pairs in a t-structure`: eight generic derived t-structure/truncation results, no requested fixed-pair assertion. Updated query `Canonical truncation triangle of Frobenius fixed pairs and Frobenius equivariance of point fibre cohomology`: eight unrelated Frobenius/isocrystal hits, no match.
- LeanSearch, `An exact functor preserving a t-structure lifts truncations to equivariant objects`: eight generic exact-functor/truncation declarations, no specialization.
- Loogle, `CategoryTheory.Functor.eTruncLTIso, CategoryTheory.Triangulated.TStructure.truncGE`: unknown first identifier. Replacement literal queries `"truncLE"` and `"truncGE"`: twelve generic complex-shape declarations each. The upstream `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso` is unknown to Mathlib's Loogle, and is instead read directly from the project's upstream source.
- Mathlib grep, `fixed.*[Tt]runc|[Tt]runc.*[Ww]eil|[Tt]runc.*[Ee]quivariant` in CategoryTheory: zero hits.
- rg in both project Lean roots for this blueprint id and the introduced declaration names: no match. Concept searches found `FixedPairTruncationOrthogonality` (a different generic assertion, not the shifted boundary/point equation), `SfCommonStageWeilCohomology` (only the existing common-stage cohomology construction), and old upstream `WeilComplex.objectProperty_truncLT`/`exists_distTriang_truncLT` on a different derived-of-Weil-sheaves category. Those do not state the item on the recorded rational/common-stage fixed-pair categories. Existing `IsoAlgebra.mapOfNatIso` is reused rather than copied.

No STATEMENT-DISPUTED issue or mathematical statement fault was found.

### Repair and validation

The required initial dry run found the retained sandbox had no item node file. Recreated it from the current base, changing lean and adding the needed notion/interface records; the present H2 repair replaces the earlier theorem dependency by the new definition owner.

The earlier canonical-shift import now fails because `Sheaf.Paper.FieldWeilShriekShiftData` has neither source nor object file on the current server (`scompile.py --source` confirms source unavailable). A minimal import reproduced that failure. This delivery removes that unavailable import and uses the existing `IntegralPullbackCompletedComparison` shift coordinates/descent, plus the canonical localization and common-stage inclusion equations. No arbitrary shift, duplicate shift construction, published source edit or launcher edit was substituted.

The full module has compiled cleanly through scompile.py both as sandbox and library-path module (approximately 13 seconds each, under the default 60-second limit). There are exactly four sorry proofs and no proved theorem in this stage-2 delivery. The prescribed delivery preflight and its repeat compilation are recorded by deliver2.py.

## Second reading by Q19

No second worker was started: the dispatcher brief forbids subagents, and the worker delivers directly for the maintainer's independent review. A final self-check found and repaired the old missing point-fibre assertions, missing specializations, shifted-boundary normalization, and the unavailable canonical-shift import. The clause mapping above is the worker's reading, not a claimed independent review.

## New nodes

`def-pod-integral-completed-comparison-data` records `existing: true` on the unchanged `Sheaf.Paper.IntegralPullbackCompletedComparison` declarations. Its primary declaration is `WeilConjectures.IntegralCompletedComparison.Comparison`; the declaration list also owns `ShiftCoordinates`, `ShiftDescent`, `roosEnd`, `productShift`, and all explicitly named definition helpers in that namespace. It cites `def-pur-integral-derived-operations` and `def-weil-derived-pullback-tensor-hom`, the coefficient/evaluation interface definition, the completed pullback, and the two completeness notions. The source is the item's blueprint exact-pullback sentence, expanded by Stacks 099N(5), 0941 and the signed cone convention 014E. Its statement describes the comparison-data type and its equations, and asserts no inhabitation. The three search kinds are recorded with actual results in mathlib_searches: LeanSearch returned eight general cochain-shift facts, LeanFinder eight generic shift-pullback declarations, Loogle twelve generic CommShift declarations, and Mathlib grep zero hits. The project has the exact definitions; the DAG has no definition owner. The earlier theorem node's helper list is not a definition owner. No declaration is redefined and no new module is needed.

## Repair of return L at 852730d93a64

H2 is repaired by adding the definition node above and replacing `lem-a1-integral-pullback-completed-comparison` in stmt_deps with it. The theorem is now in proof_deps, as requested. The item still publicly imports the existing module because its statement uses Comparison; that same import supplies the theorem for the later proof. No mathematical statement, proof plan, Lean signature or Lean source was changed. This is a dependency-only repair explicitly requested by the maintainer, not a mathematical statement correction.

Compared the retained packet with the current repository base: before this repair only lean and stmt_deps differed. The initial prescribed dry run passed at 0d81c85840b. The saved packet and returned-head description agree on the original H2 error. The report's earlier claim that the theorem owned the notion is corrected above.

Self-check of the new node against the source: levelShift is the composite termwise shift; productShift is its product followed by inverse product-preservation; roosEnd is exactly towerTransitionEndomorphism; ShiftCoordinates fixes both cocone coordinates with r.negOnePow on the second; ShiftDescent includes the good shifted representative and both derived Q comparisons; Comparison fields are intrinsic, finite, finite_normalization, chainShift, chainShift_coordinates, derivedShift, derivedShift_descent, gamma, naturality, projections, shifts. The node names each clause and claims no existence. Zero representatives and negative and zero r remain quantified; no invertibility or finiteness hypothesis was added to the comparison-data type. The previously reviewed item still covers the empty and non-separated scheme, the point case, and negative m/i/r.

The advisory about theorem-owned point equalities concerns previously recorded dependency interfaces, not a numbered repair; the point maps remain those recorded transports and eqToHom. The ambient integralDerivedPullback is reached through the new definition's cited integral-operations node and the already cited derived-pullback node. No unavailable FieldWeilShriekShiftData import is introduced. No second worker was started, in accordance with the direct-delivery brief.

## Final validation and tool refusal

The repaired item compiled cleanly via the prescribed scompile.py wrapper: sandbox compilation 12.6 seconds, library-path compilation 12.9 seconds, no diagnostics. The definition node's bracketed DAG citations match its stmt_deps exactly, and its declaration record owns 21 existing definitions/abbreviations including Comparison. Four sorry theorem proofs remain, exactly as in the retained module.

The repaired packet's prescribed deliver2.py --no-push compiled/check-loaded both relevant modules, staged exactly the item module, two node files and report, then failed the server preflight. Its concrete diagnostics were: `(b) statement correction: the item changed in proof_deps without a statement correction (proof and proof_deps change only as far as a correction of the statement forces it)` and `(e) the item's statement is corrected but the report has no non-empty section '## Statement corrected'`. This repair changes no mathematical statement: adding the comparison theorem to proof_deps is exactly what the independent return requests. The delivery wrapper explicitly permits dependency-only additions required by maintainer returns, but the server preflight rejects this one. Inventing a mathematical statement correction to pass that gate would be incorrect. Under the launcher's explicit instruction to report a wrong gate refusal and never patch or work around it, the packet is retained and no push is attempted.

## Retained-packet retry, 2026-10-21

Read the saved report and first ran the prescribed deliver2.py --no-push on the
unchanged packet. The server preflight again rejected exactly two points:
`(b) statement correction: the item changed in proof_deps without a statement
correction (proof and proof_deps change only as far as a correction of the
statement forces it)` and `(e) the item's statement is corrected but the report
has no non-empty section '## Statement corrected'`.

Compared the saved item node against the current read-only repository: only lean,
stmt_deps and proof_deps differ. The mathematical statement is verbatim unchanged,
and there is no statement_change on either node. The only proof_deps addition is
lem-a1-integral-pullback-completed-comparison, explicitly required by return L.
The new definition owner remains in stmt_deps. Reading the prescribed wrapper
confirmed its explicit permission for this dependency-only proof repair; reading
tools/node_fields.py confirmed the opposing unconditional rejection when the
statement is unchanged. No launcher or project tool was edited, no mathematical
correction was invented, and no required dependency was removed to bypass the gate.

Repeated the prescribed scompile.py on the retained delivered Lean module:
sandbox compilation 12.9 seconds; library-path compilation 12.6 seconds; exit 0,
no diagnostics. The repair packet remains ready for a corrected server gate;
no push was attempted after the failed preflight.

## Retained-packet retry after try 2, 2026-10-21

Followed the dispatcher's required order: read this retained report, then ran
`deliver2.py Q19 lem-pod-fixed-pair-truncation-cohomology --no-push` before
changing the packet. Both preliminary and sandbox compile checks passed. The
server preflight still rejects the required addition of
`lem-a1-integral-pullback-completed-comparison` to proof_deps, with the same
(b) unchanged-statement/proof_deps diagnostic and (e) missing statement-correction
section diagnostic. Nothing was pushed.

Confirmed against the current read-only repository that only lean, stmt_deps and
proof_deps differ; statement and proof remain verbatim unchanged, and neither
version has statement_change. The single proof_deps addition is required by
return L. The wrapper explicitly permits this maintainer-requested dependency-only
repair (deliver2.py lines 133–140), whereas node_fields.py lines 85–93 rejects
any proof_deps change with an unchanged statement. This is the same concrete
wrong gate refusal, not a Lean or mathematical defect. Removing the required
dependency, inventing a statement correction, or patching a gate would violate
the instructions. The repair packet is retained unchanged except for this report.

Explicit scompile.py validation also passed: sandbox 12.9 seconds, library-path
12.6 seconds, exit 0 and no diagnostics. No launcher/project tool, live source or
live node was edited, and no direct git command was run.

## Retained-packet retry after try 3, 2026-10-21

Read the retained report and first ran the prescribed unchanged-packet dry run.
Both preliminary Lean checks passed, but server preflight again rejected the
maintainer-required proof_deps addition with the same two diagnostics: (b) the
item changed in proof_deps without a statement correction; (e) no non-empty
Statement corrected section. Nothing was pushed.

Compared the packet against the current read-only repository. Only lean,
stmt_deps and proof_deps differ; statement and proof are unchanged, neither
node has statement_change, and the sole proof_deps addition is
lem-a1-integral-pullback-completed-comparison, required by return L. The saved
new definition node already owns Comparison and its helpers and is cited in
stmt_deps. Thus the requested mathematical/interface repair is retained.

Read the actual conflicting tool rules again: deliver2.py explicitly permits
maintainer-required dependency-only proof additions, whereas
check_statement_change in tools/node_fields.py unconditionally rejects the
same unchanged-statement proof_deps addition. This is a concrete wrong gate
refusal. Removing the required dependency, inventing a mathematical statement
correction or editing/bypassing a gate would violate the dispatcher brief.
No launcher/project tool or live source was edited and no direct Git command
was run. The packet remains in the sandbox for a corrected server gate.

Explicit prescribed scompile.py validation passed again: sandbox 12.9 seconds,
library-path 12.6 seconds, exit 0, no diagnostics.

## Retained-packet retry after try 4, 2026-10-21

Read the saved report and ran the required unchanged-packet dry run first.
The wrapper refreshed its current base and staged the item module, both node
records and report, but server preflight again refused the same two points:
(b) the item changed in proof_deps without a statement correction, and
(e) the item is treated as corrected but has no Statement corrected section.
No push was attempted.

Compared the saved node with the refreshed read-only repository by parsed JSON:
only lean, stmt_deps and proof_deps differ. Statement and proof are verbatim
unchanged, and neither node has statement_change. The added statement dependencies
are def-pod-integral-completed-comparison-data and def-weil-constructible-heart;
none is removed. The sole proof dependency addition is
lem-a1-integral-pullback-completed-comparison, expressly required by return L.
The new definition owner remains existing:true on
WeilConjectures.IntegralCompletedComparison.Comparison.

Confirmed the conflicting tool rules by reading them: deliver2.py explicitly
allows a maintainer return to add proof dependencies while the statement remains
verbatim; tools/node_fields.py check_statement_change rejects that exact change.
There is no mathematical correction to record. No gate was edited or bypassed,
no required dependency was removed, and no statement change was invented.

The explicit prescribed scompile.py check passed with exit 0 and no diagnostics:
sandbox compilation 14.7 seconds; library-path compilation 17.1 seconds.
The repaired packet remains retained for correction of the server gate.

## Retained-packet retry after try 5, 2026-10-21

Read the saved report and first ran the required unchanged-packet dry run.
Its preliminary and sandbox Lean checks passed; server preflight again refused
(b) the unchanged-statement proof_deps addition and (e) the absent Statement
corrected section. No delivery was pushed.

Compared parsed sandbox/current-base node records: only lean, stmt_deps and
proof_deps differ. Statement and proof are unchanged, with no statement_change.
The sole added proof dependency is lem-a1-integral-pullback-completed-comparison,
required by return L. The new existing:true definition owner still owns
Comparison, ShiftCoordinates, ShiftDescent and field helpers and is cited by
the item. No required mathematical repair was removed.

Read the concrete conflicting code: deliver2.py explicitly permits a maintainer
return to add proof dependencies with the statement unchanged, whereas
check_statement_change in tools/node_fields.py rejects this exact addition.
The fresh failed dry run confirms that this contradiction persists on the server.
Under the explicit prohibition on editing or bypassing gates, the packet cannot
be delivered until that tool refusal is repaired. No statement correction was
invented and no tool or read-only repository file was edited.

Explicit scompile.py validation passed with exit 0 and no diagnostics:
sandbox 14.7 seconds; library-path module 17.1 seconds. The repaired packet
remains retained in the sandbox.

## Retained-packet retry after try 6, 2026-10-21

Read the saved report and ran the required unchanged-packet dry run first.
The wrapper completed its two preliminary Lean checks and staged the module,
both node records and report. Server preflight again rejected exactly (b) the
unchanged-statement proof_deps addition and (e) the absent Statement corrected
section. Exit status was 1; nothing was pushed.

A fresh parsed comparison with the wrapper-refreshed shared repository confirms
that only lean, stmt_deps and proof_deps differ. No dependency is removed. The
sole proof_deps addition is lem-a1-integral-pullback-completed-comparison, required
by return L; the mathematical statement and proof remain unchanged, and neither
node has statement_change. The existing:true definition owner still records
Comparison, ShiftCoordinates, ShiftDescent and the field helpers, and the item
cites it in stmt_deps.

Read the conflicting rules directly: deliver2.py explicitly authorizes a
maintainer-return dependency-only proof repair, but tools/node_fields.py
check_statement_change rejects any proof_deps change when the statement is
unchanged. The fresh server diagnostic confirms this wrong refusal persists.
The requested H2 repair is retained. No mathematical correction was invented,
required dependency removed, gate bypassed or tool edited. The dry run's
successful preliminary Lean checks need no repeated compile without a source
change. Delivery remains blocked by the server preflight tool.

## Retained-packet retry after try 7, 2026-10-21

Read the saved report and first ran the prescribed unchanged-packet
`deliver2.py Q19 lem-pod-fixed-pair-truncation-cohomology --no-push`.
The preliminary Lean checks passed and the wrapper staged the item module,
both node records and report. Server preflight exited 1 with the same two
reasons: (b) the item changed in proof_deps without a statement correction;
(e) the item is classified as corrected but has no Statement corrected section.
Nothing was pushed.

A fresh parsed comparison against the current read-only repository confirms
that only lean, stmt_deps and proof_deps differ. The mathematical statement
and proof remain verbatim unchanged, and neither node has statement_change.
The added statement dependencies are def-pod-integral-completed-comparison-data
and def-weil-constructible-heart; no dependency is removed. The sole added
proof dependency is lem-a1-integral-pullback-completed-comparison, expressly
required by return L. The existing:true definition owner still owns Comparison,
ShiftCoordinates, ShiftDescent and the field helpers and cites both definition
nodes required by the return.

Read the conflicting code directly: deliver2.py permits maintainer-requested
proof dependency additions without changing the statement, while
check_statement_change in tools/node_fields.py rejects exactly that change.
The fresh server diagnostic confirms the refusal persists. No source change
requires further compilation after the successful preliminary checks. No
mathematical statement correction was invented, required dependency removed,
gate bypassed or tool edited. The repaired packet remains in the sandbox;
delivery is blocked by the server preflight tool.


## Current retained-packet retry, 2026-10-21

Read the retained report and ran the prescribed initial dry run without changing
its packet. Repeated it with output retained in dry-run-current.log. The repeat
completed both preliminary Lean checks, staged the four delivery files, and
exited 1 at server preflight. It reported exactly:

- `(b) statement correction: the item changed in proof_deps without a statement correction (proof and proof_deps change only as far as a correction of the statement forces it)`
- `(e) the item's statement is corrected but the report has no non-empty section '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)`

Fresh parsed comparison against the wrapper-refreshed read-only repository found
only lean, stmt_deps and proof_deps differ. The statement and proof are unchanged.
The definition owner and constructible-heart node are the two added statement
dependencies; the sole added proof dependency is the comparison theorem required
by return L. No dependency is removed. The existing definition owner names
Comparison, ShiftCoordinates, ShiftDescent, productShift, roosEnd and their
helpers, and cites both definition dependencies expressly required by L.

Read deliver2.py lines 133–140: maintainer-requested dependency-only proof repairs
are permitted without a mathematical statement change. Read tools/node_fields.py
lines 85–93: that same proof_deps change is unconditionally rejected when the
statement remains unchanged. This is the actual tool refusal, not a missing
notion or a Lean failure. No artificial statement correction, removal of the
required proof dependency, modification of launcher/project tools, or gate bypass
was attempted. The saved H2 repair is retained; nothing was pushed.

## Dispatcher retained-packet check, 2026-10-21

Read the saved report and ran the prescribed initial deliver2.py --no-push
without changing the packet. The server Lean checks passed. Preflight exited 1
with the same two concrete diagnostics: (b) proof_deps changed without a
statement correction; (e) missing non-empty Statement corrected section.
No push occurred.

Parsed comparison with the current read-only base confirms only lean, stmt_deps
and proof_deps differ. The statement and proof remain unchanged; neither node
has statement_change. The sole proof_deps addition is the comparison theorem
expressly required by return L. The saved new existing:true definition owner
records Comparison, ShiftCoordinates, ShiftDescent, productShift, roosEnd and
the field helpers, and cites both definitions required by L.

Read deliver2.py lines 133–140 and tools/node_fields.py lines 85–93 directly:
the wrapper expressly permits this maintainer-return dependency-only repair,
but server preflight rejects it. This is a persistent wrong tool refusal.
No tool was edited or bypassed, no required dependency removed, and no
mathematical statement correction invented. No Lean source changed, so the
successful dry-run Lean checks require no additional compilation. The repaired
packet is retained for a corrected gate.

## Current retained-packet repair check, 2026-10-21

Ran the prescribed initial deliver2.py --no-push on the retained packet, then
repeated with output saved in dry-run-current.log. The repeat completed the
server Lean checks and exited 1 at preflight with the same two diagnostics:
(b) proof_deps changed without a statement correction; (e) missing non-empty
Statement corrected section. No push occurred.

Compared parsed node records with the freshly refreshed read-only repository:
only lean, stmt_deps and proof_deps differ. The sole proof_deps addition is
lem-a1-integral-pullback-completed-comparison, expressly requested by return L.
The mathematical statement and proof remain unchanged. Verified the existing
definition owner records Comparison, ShiftCoordinates, ShiftDescent, roosEnd,
productShift and the field helpers, with both required definition dependencies.

Read the relevant launcher wrapper and project validator directly.
deliver2.py lines 133–140 authorize maintainer-return dependency-only additions;
tools/node_fields.py lines 85–93 reject this unchanged-statement addition.
The refusal is in the tools. The required repair is retained without inventing
a statement correction, removing the required dependency or altering tools.


## Retained-packet retry, 2026-10-22

Read the retained report and first ran the prescribed unchanged-packet
`deliver2.py Q19 lem-pod-fixed-pair-truncation-cohomology --no-push`.
The wrapper completed its preliminary Lean checks and staged the four delivery
files. Server preflight exited 1 with the same two diagnostics: (b) the item
changed in proof_deps without a statement correction; (e) missing non-empty
Statement corrected section. Nothing was pushed.

Fresh parsed comparison with the wrapper-refreshed read-only base confirms only
lean, stmt_deps and proof_deps differ. Statement and proof are verbatim unchanged;
neither node has statement_change. No dependency is removed. The two statement
dependency additions are def-pod-integral-completed-comparison-data and
def-weil-constructible-heart. The sole added proof dependency is
lem-a1-integral-pullback-completed-comparison, expressly required by return L.
The definition owner records Comparison, ShiftCoordinates, ShiftDescent,
productShift, roosEnd and the field helpers, and cites both definitions required
by the return. The requested H2 repair is retained.

Read the conflicting tool code directly: deliver2.py lines 133–140 explicitly
permit maintainer-requested dependency-only proof additions;
tools/node_fields.py check_statement_change rejects exactly this change while
the statement remains unchanged. This is a concrete tool refusal. No tool was
edited or bypassed, no required dependency removed, and no artificial statement
correction invented. No Lean source changed, so the successful preliminary
checks require no repeated compilation. The packet remains in the sandbox.

## Fresh retained-packet check, 2026-10-22

Read the retained report and ran the prescribed initial unchanged-packet
`deliver2.py Q19 lem-pod-fixed-pair-truncation-cohomology --no-push`.
The wrapper completed its preliminary Lean checks and staged the four delivery
files, then server preflight exited 1: (b) proof_deps changed without a
statement correction; (e) missing non-empty Statement corrected section.
Nothing was pushed.

Fresh parsed comparison with the refreshed read-only base confirms only lean,
stmt_deps and proof_deps differ. Statement and proof are unchanged and neither
node has statement_change. The sole proof dependency addition is
lem-a1-integral-pullback-completed-comparison, required by return L. The
existing:true definition owner retains Comparison, ShiftCoordinates,
ShiftDescent and field helpers and cites both required definition nodes.

Read the conflicting rules directly: deliver2.py lines 133–140 permit this
maintainer-requested dependency-only repair, but tools/node_fields.py
check_statement_change rejects it. The fresh server refusal persists. No
mathematical correction was invented, required dependency removed, or gate
edited or bypassed. No Lean source changed; the dry run's successful Lean
checks require no repeated compile. The repaired packet remains retained.

## Retained-packet verification, 2026-10-22

Ran the required initial `deliver2.py Q19
lem-pod-fixed-pair-truncation-cohomology --no-push` on the saved packet.
Its preliminary server Lean checks passed. Preflight exited 1 without pushing:
(b) proof_deps changed without a statement correction; (e) missing non-empty
Statement corrected section.

A fresh parsed comparison with the refreshed read-only base confirms that only
lean, stmt_deps and proof_deps differ. Statement and proof are unchanged;
neither node has statement_change. No dependency was removed. The sole added
proof dependency is lem-a1-integral-pullback-completed-comparison, explicitly
required by return L. The saved definition owner records Comparison,
ShiftCoordinates, ShiftDescent, productShift, roosEnd and the helpers, and cites
both definition dependencies required by the return.

Read the conflicting code directly: deliver2.py permits maintainer-requested
proof dependency additions without a statement change; check_statement_change
in tools/node_fields.py rejects this exact addition. This fresh refusal is a
tool failure. No required dependency was removed, mathematical correction
invented, or gate edited or bypassed. No Lean source changed, so the successful
preliminary checks need no repeated compilation. The repaired packet is retained.


## Pipeline maintenance resolution, 2026-10-22

Server maintenance commit `1ffa2f881a226613049b809124067cbff8d8b80b` records
`lem-a1-integral-pullback-completed-comparison` in the existing shift proof
step (Step 4) and in the item's `proof_deps`. It implements the independent
return at `852730d93a64` without changing the statement, any proof text,
or any Lean declaration. The proof-dependency union is consistent.

The earlier blocked dry runs above describe the old base. They exposed an
inconsistency between deliver2.py's additive proof-dependency permission
and the server's statement-correction validator. The validator is a
protected landing tool and was not edited. The authorized live DAG
metadata repair makes the retained packet's proof dependencies equal to
the base. The sandbox's proof-step uses have been synchronized as well.
Rebase on the current server branch, retain the new definition owner and
its stmt_deps citation, and run the normal dry run and delivery. Do not
invent a mathematical statement correction for this metadata repair.


Maintenance validation: a frozen copy of this packet passed the normal
`deliver2.py Q19 lem-pod-fixed-pair-truncation-cohomology --no-push` after
the server metadata commit. Result: `OK (dry run): commit 932efc7b36d
passes the preflight and compiles; nothing pushed`. The module and existing
declaration probes were checked individually on the server. The next worker
can use the normal delivery command; this maintenance run did not push a
worker delivery or modify dispatcher state.

## Successful retained-packet validation, 2026-10-21 UTC

The first prescribed dry run reproduced the former proof_deps preflight refusal.
A fresh comparison after the wrapper refreshed the shared base found that
lem-a1-integral-pullback-completed-comparison is now already in the base's
proof_deps. Repeating the unchanged-packet dry run therefore passed both server
Lean checks and preflight: OK at f54593a718b. The historical refusals above are
resolved by the current base; no gate or mathematical statement was changed.

Final self-check with the module and both node records open: the definition
owner records the unchanged Comparison, ShiftCoordinates, ShiftDescent,
productShift, roosEnd and field helpers, citing both definitions requested by
return L. The item cites that definition owner in stmt_deps and the comparison
existence theorem only in proof_deps. Its natural-language statement and proof
remain unchanged. The four theorem signatures and their sorry-only proofs are
retained; the canonical truncation and point-transport equations remain as
independently checked in return L. No Lean source changed during this retry.
The final packet is sent through the prescribed dry run and delivery wrappers.
