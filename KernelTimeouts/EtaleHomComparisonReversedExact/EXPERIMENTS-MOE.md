# MISMATCH ORIGIN AND BOUNDARY STABILITY REPORT

Case: `EtaleHomComparisonReversedExact`
Lean / Mathlib revision: Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; current tree `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`
Declaration / root conversion: `etaleHomComparison_reversedExact_commShift_component`; application argument 26 (`hv`) of `derivedTensorHomShiftComparison_component`
Source snapshot: `8ca2e912b93`; current-master instance rename is mechanical and does not change the theorem statement/body.

## 1. STAGE SNAPSHOTS

S0 source: The source writes `hv : IsEtaleHomTranspose X φ M v` and passes `hv` directly as argument 26. It also writes hidden providers including `inferInstance` for `Functor.Additive` and a local provider for `scalarExtension.Additive`.

S1 macro-expanded: `IsEtaleHomTranspose X φ M v` has no macro-generated change. S0 and S1 syntax are identical in `syntax.snapshot`.

S2 elaborated: The original local application has actual argument-26 type `IsEtaleHomTranspose X φ M v`; after the first 25 arguments are instantiated, the expected domain is a `forall K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)), ...`. The actual outer Expr is an application of `IsEtaleHomTranspose`; the expected outer Expr is `forall:default`. `Kernel.isDefEq` succeeds after reduction. The transported local lambda `(fun K => by transport_exact hv K)` has `forall/forall` type and is syntactically equal to the expected domain (`moe_compare`: `first-divergence=none`).

Hidden/preceding arguments recorded by the local audit include `ModuleCat.instMonoidalPreadditive` at binders 6 and 15, `scalarExtension` at 20, inferred `Functor.Additive` at 21, `etaleHomScalarCommShift` at 22, `etaleHomTensorComparison` at 23, `DerivedCategoryModule`/`Quiver.Hom` dependent arguments at 24--25, and later shift/normalization arguments. These non-syntactic entries are provider/type paths, not proof of a distinct provider choice by themselves.

S3 finalized: The imported declaration exposes no pre-finalization term. Batch 0 marks this `finalization-observable-only`; the stored theorem is a theorem constant with no imported pre-finalization value available. No auxiliary declaration was recorded in the bounded S4 snapshot.

S4 stored ConstantInfo: `IsEtaleHomTranspose` is a regular `def` with hint `regular:34`; `DerivedCategoryModule` is an `abbrev`; `scalarExtension` is an `abbrev`; `etaleHomScalarCommShift` is `regular:27`; `etaleHomTensorComparison` is `regular:33`; `ModuleCat.instMonoidalPreadditive` is an opaque theorem; `DerivedCategory.instMonoidalCategory` is `regular:26`; the target theorem is opaque. The stored target type begins with the expected implicit `A`, `B`, ring, and scheme telescope. The stored theorem value is a lambda (`p4_value.snapshot`), but its proof body was not traversed.

S5 Kernel root pair: The exact local root is the type of `hv` versus the instantiated domain at application argument 26. `Kernel.isDefEq` returns true. The original READY4.2 root has 3,180,470 recursive calls, maximum depth 111, 12,098.651 ms comparison-exclusive and 11,714.111 ms reduction-exclusive. The transported pair returns true with 7,039 calls and 31.957 ms total root time.

S6 Kernel-exposed descendants: READY4.2 classifies the original root as M1 propagation: 2,390,795 M1 calls / 99.762% of comparison-exclusive time, 22 M2 calls / 0.001%, and 789,652 Matched calls / 0.236%. Dominant descendants follow `DFunLike.coe -> NatTrans.app -> tensorLeft` and dependent/proof-position paths. The root has 132,807 Pi-domain events, 60,717 proposition comparisons, and 412,714 instantiations. No single binder field is isolated by the available counters.

## 2. FIRST DIVERGENCE

Exact left/right expressions: left `IsEtaleHomTranspose X φ M v`; right the expanded expected `forall K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)), ...` domain after the first 25 helper arguments are supplied.

Expr path: `root`; the first comparer record is `kind=kind left=app right=forall:default`. The left head is the regular `AlgebraicGeometry.Etale.IsEtaleHomTranspose` constant with 8 arguments. The right quantified domain uses `DerivedCategory`, `ObjectProperty.FullSubcategory.category`, `Scheme.smallEtaleTopology`, `HasDerivedCategory.ofIsGrothendieckAbelian`, and category instances.

Earliest stage present: S0/S1 source/API vocabulary. The source names a compact predicate while the helper expects its expanded dependent domain. S2 preserves this and fixes concrete hidden arguments. It is latent behind the regular `IsEtaleHomTranspose` head until Kernel unfolding; then it is active at the dependent Pi-domain comparison.

M0 / M1 / M2 consequence: the application-domain mismatch is M0. Descendants are overwhelmingly M1 (99.762% of comparison-exclusive calls); M2 is negligible (22 calls). The nested difference is `DerivedCategoryModule` abbrev versus raw `DerivedCategory` regular representation after unfolding `IsEtaleHomTranspose`.

## 3. ORIGIN

Source-authored: **demonstrated**. The source explicitly writes the named predicate and direct helper application. The source-level expanded control writes the `forall K` premise instead.

Macro-generated: **not observed**. S0 and S1 are identical.

Elaborator-selected: **assignments observed, causal contribution not demonstrated**. Trace records show synthesis selecting `ModuleCat.instMonoidalPreadditive` for both module categories and assigning scalar extension, comm-shift, category, and derived-category terms. These are concrete S2 arguments, but no alternative provider selection was shown to change the root Expr or frozen cost. The compact-vs-expanded predicate choice is source-authored. Meta `default` or `all` is required for the actual/expected domain (`none`, `reducible`, and `instances` fail); no successful perturbation produced a different final Expr.

Declaration-finalization-generated: **not observed**. The divergence is present in S0/S1 and S2. The imported target is opaque at S4; no evidence attributes the trigger to proof abstraction or generated declarations.

Environment/import-frozen: **partly**. The helper theorem, predicate, abbrevs, and provider declarations are imported and their S4 hints are fixed. Current local priorities cannot rewrite those stored declarations.

Kernel-exposed: **demonstrated as exposure, not origin**. The regular predicate body is unfolded during Kernel comparison; its quantified domain exposes the abbrev/raw domain mismatch and dependent equality descendants.

Unknown / mixed: The exact internal first reduction order after unfolding and the contribution of each later provider leaf remain unknown.

## 4. ELABORATOR PROVENANCE

Relevant metavariables: The local trace records assignments for `MonoidalPreadditive (ModuleCat A/B)` to `ModuleCat.instMonoidalPreadditive`; `Functor.Additive` for scalar extension to an inferred instance; `(scalarExtension φ X).CommShift ℤ`; category instances for `DerivedCategory (Sheaf ...)`; and dependent object terms such as `(scalarExtension φ X).obj ?m`.

Instance synthesis choices: Candidate search for `MonoidalPreadditive (ModuleCat A/B)` lists and selects `@ModuleCat.instMonoidalPreadditive`. Category synthesis selects `instCategoryDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A/B))`; derived-category preadditive synthesis selects `DerivedCategory.instPreadditive` through `HasDerivedCategory.ofIsGrothendieckAbelian`.

Implicit arguments: The helper application has 34 arguments. Binders 6, 15, 20, 22, 23, 24, 25, and 26 are relevant hidden/provider/dependent positions. The original argument 26 is the local `hv` fvar; the transported control changes exactly that argument to a lambda while retaining the first 25 arguments and local context.

Coercions: The S6 path and existing READY4 audit record `DFunLike.coe`, `EquivLike.coe`, `Equiv.toFun`, `Equiv.invFun`, and `NatTrans.app` descendants. These are Kernel-exposed descendants of the dependent equality body, not a separately demonstrated source coercion choice at S0.

Transparency modes: `trace.Meta.isDefEq.transparency` records local escalation, including `instances -> implicit`, during instance and expected-type unification. A fresh direct replay of the actual `hv` type against the instantiated domain gives `none=false`, `reducible=false`, `instances=false`, `default=true`, `all=true`. This identifies the required Meta transparency for the constraint but does not change the final stored Expr.

Expected types / local context: The actual type is `IsEtaleHomTranspose X φ M v`; the expected type is the helper binder-26 domain after the first 25 concrete arguments. The expected quantified object is raw `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))`, while the named predicate uses `DerivedCategoryModule A X` (an abbrev).

Evidence that a choice changed the final Expr: **not demonstrated**. The original and transported variants differ because the source premise differs; transparency changes alone were not observed to select a different final expression. The elaborator contribution is plausible for provider details, not causal for the earliest root divergence.

## 5. KERNEL INPUT AND COST

Stored type/value: The target S4 type is stored as an opaque theorem type. Its value is a lambda in the imported environment, but the proof body was not traversed. The local application S2 pairs are retained in `p4_probe.snapshot` and `p4_transport.snapshot`.

Kernel reducibility hints: `IsEtaleHomTranspose regular:34`; `DerivedCategoryModule abbrev`; `scalarExtension abbrev`; `etaleHomScalarCommShift regular:27`; `etaleHomTensorComparison regular:33`; `DerivedCategory.instMonoidalCategory regular:26`; target and helper theorems opaque. These metadata differences explain why unfolding exposes the abbrev/raw domain boundary, but they are not an isolated metadata-only replay.

Exact root pair: `hv` type versus helper expected domain at argument 26, under `derivedTensorHomShiftComparison_component` with the first 25 arguments instantiated.

Recursive calls / shares: Original: 3,180,470 calls, depth 111, comparison-exclusive 12,098.651 ms, reduction-exclusive 11,714.111 ms; M1 2,390,795 / 99.762%, M2 22 / 0.001%, Matched 789,652 / 0.236%. Transported: 7,039 calls, depth 124, 14.687 ms comparison-exclusive, 17.270 ms reduction-exclusive, 31.957 ms total. Expanded predicate restoration: 3,179,834 calls, 11,978.789 ms comparison-exclusive, 11,655.117 ms reduction-exclusive. The expanded control reproduces the original path.

Relevant comparison path: dependent Pi-domain comparison, then equality/application/projection descendants through `DFunLike.coe`, `NatTrans.app`, `tensorLeft`, derived-category internal-Hom and additive structure fields. M1 propagation dominates; M2 is negligible.

## 6. CHEAP-BOUNDARY INVENTORY

Boundary: `IsEtaleHomTranspose` named predicate (`P4-B1`)

Boundary kind: Named proposition regular `def`.

Current fast conversion: The transported premise `(fun K => by transport_exact hv K)` has a matching `forall/forall` expected type and completes the helper application in 31.957 ms / 7,039 calls.

Stored outer head: Transported S2 outer head is `forall:default`; original S2 actual head is `app` of `IsEtaleHomTranspose`.

Kernel hints: `IsEtaleHomTranspose regular:34`; `DerivedCategoryModule abbrev`; expected raw `DerivedCategory` is regular.

Why currently cheap: Transport presents the helper with its exact quantified domain, avoiding the named-predicate unfold and wrapper/raw dependent comparison.

Puncture operations: Direct `exact` handoff of `hv`; unfolding the predicate; concrete `simp`/`rw` exposing `DerivedCategoryModule`; raw proof reconstruction.

Re-exposure result: **Yes.** Direct `hv` takes 23.813 s / 3,180,470 calls; explicit expanded predicate takes 23.634 s / 3,179,834 calls. The named predicate alone is not protection.

Future drift risks: Expanding the predicate in a theorem statement, changing the abbrev or raw category vocabulary, or replacing whole-proposition transport with direct `exact` can reactivate the M1 tree. Status: **fragile**.

Boundary: Whole-proposition transport (`P4-B2`)

Boundary kind: Theorem/transport boundary around the complete dependent proposition.

Current fast conversion: `transport_exact hv K` gives the helper's expected domain at each `K`; no M0-preserving descendant-only cut was type-correct.

Stored outer head: `forall/forall`, structurally identical after metavariable instantiation. No new declaration hint; this is an expression-level transport.

Puncture operations: Rewrite the concrete goal back to the named predicate, reconstruct the raw proof proposition, or expose the dependent body under the original fvar.

Re-exposure result: **Yes**, by original versus transported counters. Future risk is a convenience lemma or direct `rfl`/`simp` proof that retains the named predicate without transporting the whole proposition. Status: **fragile but effective**.

Boundary: Hidden provider sharing (`P4-B3`)

Boundary kind: Explicit/local provider and imported category/functor instance path.

Current fast conversion: The transport control retains the same first 25 arguments and local additive/comm-shift providers; no provider-only replacement was type-correct without changing the root telescope.

Stored outer heads: `ModuleCat.instMonoidalPreadditive`, `scalarExtension`, `etaleHomScalarCommShift`, and category/derived-category instances. Hints are opaque/theorem for the module provider, abbrev for scalar extension, and `regular:26` for `DerivedCategory.instMonoidalCategory`.

Puncture operations: Replace a local provider with an independently inferred structure, change category arguments, or mix `DerivedCategoryModule` and raw `DerivedCategory` vocabulary.

Re-exposure result: Not isolated. Existing controls show provider differences in descendants, but no M0-preserving provider-only perturbation was constructible. Status: **untested/fragile risk**, not a demonstrated primary trigger.

## 7. CONTROL RESULTS

Original: Direct `hv`; S2 outer `app` versus expected `forall`; S5 true. READY4.2: 3,180,470 calls, 23.813 s root, M1 99.762% of comparison-exclusive time.

Perturbed elaboration: `(fun K => by transport_exact hv K)` at exactly argument 26. S2 type becomes `forall/forall`, `moe_compare` reports no divergence, S5 true. READY4.2: 7,039 calls, 31.957 ms root.

Frozen replay: `moe/P4Frozen.lean` elaborates both source variants in one
scratch declaration, freezes their argument-26 actual/expected Exprs, then
calls `Kernel.isDefEq` for each with the same Environment and local context.
F0 (`h0`, direct `hv`) has actual/expected hashes
`1172892286`/`2832094282`, is structurally unequal, and succeeds in READY4.2
root 2749 with 3,180,439 calls / 26,052.431 ms. F1 (`h`, transported
premise) has equal hashes `2832094282`/`2832094282` and succeeds in root
2750 with one call / 0.013 ms. These are the exact frozen local pairs; the
source premise changed, so this is not an Elaborator-only perturbation.

Kernel-metadata control: No valid F2 metadata-only control was constructed. The S4 hint inventory records relevant metadata, but expanded-predicate restoration changes expression exposure as well as reduction and is not metadata-only evidence.

Same root obligation preserved? Yes for the transported helper application and the full theorem control in existing `After.lean`; the transported diagnostic keeps all first 25 arguments and changes only argument 26. Original and expanded controls preserve the expensive root shape.

What changed? Only the supplied dependent premise representation: named `IsEtaleHomTranspose X φ M v` versus a lambda whose proposition is the helper's instantiated `forall` domain. Hidden providers and local context remain unchanged in the transport control.

## 8. CONCLUSION

Earliest divergence stage: S0/S1 source/API expression boundary, retained at S2; the first active Kernel exposure is after unfolding `IsEtaleHomTranspose` at the argument-26 dependent Pi domain.

Most likely origin: Source-authored compact predicate versus helper raw quantified domain, with imported environment-frozen definitions and reducibility hints determining exposure.

Elaborator contribution: **plausible, not demonstrated as causal for the root**. Instance synthesis and metavariable traces show concrete hidden provider assignments and a default/all transparency requirement. No transparency perturbation changed the final Kernel Expr; no alternate provider expression with the same obligation was isolated.

Kernel contribution: **confirmed**. Whole-proposition transport removes the deep M1 propagation tree. The original root is 99.762% M1 by comparison-exclusive calls, with negligible M2.

Current cheap-but-fragile boundaries: whole-proposition transport; the named `IsEtaleHomTranspose`/raw-domain interface; hidden provider sharing and consistent derived-category vocabulary.

What remains uncertain: exact reduction order after predicate unfolding; whether one hidden provider leaf materially amplifies the M1 tree; and a metadata-only F2 replay. The report does not attribute the root to declaration finalization or proof abstraction.

## Audit note and Batch 2 boundary test

The earlier phrase "provider assignments demonstrated, selection not" was
ambiguous: the trace does name selected instances, but no *alternate* provider
selection was observed to cause the root divergence. The earliest compact
predicate versus expanded-domain split is at S0/S1. The imported S3 snapshot
cannot establish S2/S4 identity. The targeted fresh transparency trials are
negative for a changed final Expr: lower modes fail, `default`/`all` succeed.
E3 puncture: replace the type-correct whole-proposition transport with direct
`hv`, or expand the predicate at the same argument-26 obligation. The saved
restoration has 3,180,470 calls (expanded: 3,179,834), versus 7,039 for the
transport. This is an expression-level boundary test, not provider isolation.
The same-context F0/F1 replay above further confirms 3,180,439 versus one
Kernel call for the frozen domain pairs; see `moe/P4Frozen-results.md`.
