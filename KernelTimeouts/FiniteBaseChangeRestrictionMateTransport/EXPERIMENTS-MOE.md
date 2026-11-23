# MISMATCH ORIGIN AND BOUNDARY STABILITY REPORT

Case: `FiniteBaseChangeRestrictionMateTransport`
Lean / Mathlib revision: Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); current measurement tree `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`
Declaration / root conversion: `finite_base_change_restriction_mate_transport`; private `transport_from_unit`, argument 49 (`hb`)
Source snapshot: `0676f555de6`; conversion record `FB-hb-49-v1`

## 1. STAGE SNAPSHOTS

S0 source: The supplied proof is the concrete `h` premise in the theorem application. The helper application supplies 48 preceding category, instance, equivalence, adjunction, functor, isomorphism, and mate arguments before `hb`. The expected domain is therefore dependent on those actuals.

S1 macro-expanded: No relevant notation expansion was found. The source forms remain `Scheme.ProEt moeX` and `Site .ordinary moeX` in the isolated pair probe.

S2 elaborated: Fresh `#moe_pair` output records the left as `app (const AlgebraicGeometry.Scheme.ProEt) moeX` and the right as `app (app (const SheafOfModules.OpenTensorNormalization.Site) (const Mode.ordinary)) moeX`. `#moe_compare --stage S2 --left-side L --right-side R` reports first divergence `root/fn`, `kind=kind`, left `const`, right `app`. Both sides share the `moeX` argument and the root comparison succeeds by kernel reduction.

S3 finalized: The imported declarations expose only finalization-observable data. No generated proof constant was observed on the captured first mismatch path; the local `h` proof is a premise and the expensive conversion is its proposition type against the instantiated helper binder.

S4 stored ConstantInfo: `Site` is a regular definition with hint `regular:20`; `Scheme.ProEt` is regular with hint `regular:19`. The stored `Site` value contains a mode matcher whose ordinary branch is `ProEt`; the stored type/value snapshots are in `moe/snapshot.txt`.

S5 Kernel root pair: Both sides are `forall M : FiniteModules A X', Eq ...` squares. The first active difference is in the `Quiver.Hom` type below `ProjectionRestriction.Mod`: supplied `Scheme.ProEt X` versus expected `Site .ordinary X`.

S6 Kernel-exposed descendants: The checked root has 239,340,712 recursive calls, maximum depth 87, 54.398% M1 calls / 72.869% M1 exclusive-time share, 25.661% M2 time share, and 1.419% Matched time share. The main repeated path is `CategoryStruct.comp -> LinearMap.comp -> PresheafOfModules.Hom.proj -> NatTrans.app`; the first Site exposure is a delta of the regular `Site` body followed by the ordinary mode match. The root is comparison-dominated: 0.076 s WHNF-exclusive versus 813.896 s comparison-exclusive in the counters run.

## 2. FIRST DIVERGENCE

Exact left/right expressions: `Scheme.ProEt X` versus `Site .ordinary X`, embedded in the first argument of `Quiver.Hom` under `ProjectionRestriction.Mod` in the dependent `hb` proposition. The equality skeleton and `FiniteModules` binder agree; the site difference repeats on both equality sides.

Expr path: isolated S2 pair `root/fn`; in the instantiated `hb` audit, `forall` / `Eq` / `Quiver.Hom` / `Mod` / site argument.

Earliest stage present: S0, unchanged at S1 and S2. It is active at S5 when the concrete proof is checked against the dependent binder; the mode matcher is latent until Kernel reduction.

M0 / M1 / M2 consequence: M0 is the single root entry at `hb`. M1 is the repeated dependent comparison continuation (130,197,227 calls in the READY4.2 aggregate). M2 is the reduction cascade (40,495,866 calls in the corresponding aggregate). The exact M1/M2 shares are aggregate provenance labels, not a per-site cost attribution.

## 3. ORIGIN

Source-authored: **yes**. The source theorem uses the concrete Pro-etale square while the generic helper binder stores the mode-indexed `Site` representation.

Macro-generated: **not observed**.

Elaborator-selected: **not demonstrated**. The isolated source spellings already differ; no changed metavariable assignment or instance choice was found that explains the first head difference.

Declaration-finalization-generated: **not the first origin**. The mismatch is present in the proposition before any proof abstraction could affect the value.

Environment/import-frozen: **yes for the helper declaration and Site/ProEt definitions**. Imported stored declarations fix their types, values, and reducibility hints before the current probe.

Kernel-exposed: **yes, for the latent body**. Unfolding stored `Site` exposes its mode matcher and ordinary branch; this explains a downstream reduction event, not the source of the representation difference.

Unknown / mixed: The concrete category-instance continuation (`Scheme.instCategoryProEt` versus `instCategorySite`) is a plausible amplifier, but its exclusive cost was not isolated.

## 4. ELABORATOR PROVENANCE

Relevant metavariables: The `hb` expected proposition is created after the first 48 helper arguments are instantiated. The head audit reconstructs this exact dependent domain; no separate assignment record for its site leaf is available.

Instance synthesis choices: The supplied path uses `Scheme.instCategoryProEt`; the expected path uses `instCategorySite` after `Site .ordinary` is exposed. The local category/functor hierarchy is data-bearing, but no candidate trace identifies a different current-file choice as the origin.

Implicit arguments: `Site` carries the explicit mode and scheme; the helper's quantified binder carries the abstract category/functor/equivalence parameters. The concrete specialization fixes them through the preceding actual arguments.

Coercions: The root is a dependent proposition conversion. `.app`/`.hom` notation does not establish a projection-trigger origin; no first-path `Expr.proj` was observed.

Transparency modes: The source uses `backward.isDefEq.respectTransparency` and `.types`; no targeted transparency constraint with a changed assignment was identified. A `unif_hint` for `Site .ordinary X ≟ X.ProEt` produced the same normalized actual/expected pair digest (`695947a17c9ebb043bf4449d783c07a1f4c5a89a5a18c39c8b7d317e39ce382a`) and the full checked run retained 239,340,712 calls, 150,477,480 failure calls, and 19,747,209 lazy-delta calls.

Evidence that a choice changed the final Expr: **none**. The hint audit is negative evidence for an elaborator-induced Kernel-input change; the source/API representation difference remains.

## 5. KERNEL INPUT AND COST

Stored type/value: The helper's expected `hb` type is a `forall M : FiniteModules A X'` equality over abstract instantiated categories; the supplied `h` has the same binder shape with concrete `Scheme.ProEt`-based morphism types.

Kernel reducibility hints: `Site regular:20`; `Scheme.ProEt regular:19`. `Site` is the mode-indexed regular `def`; its ordinary body reduces to `ProEt`.

Exact root pair: `hb` argument 49 of `transport_from_unit`, after 48 actuals.

Recursive calls: 239,340,712; max depth 87; comparison-exclusive 813.896 s; WHNF-exclusive 0.076 s in the counters root. The root's failure branch has 150,477,480 calls.

M1/M2/Matched shares: M1 54.398% of calls and 72.869% of time; M2 25.661% of time; Matched 1.419% of time. These are the three-repeat READY4.2 aggregate labels.

Relevant path: dependent `CategoryStruct.comp -> LinearMap.comp -> PresheafOfModules.Hom.proj -> NatTrans.app`, with repeated `NatTrans.app` descendants.

## 6. CHEAP-BOUNDARY INVENTORY

Boundary: `B-SITE`

Boundary kind: Named regular data definition (`Site mode X`).

Current fast conversion: `Site .ordinary moeX` versus `Scheme.ProEt moeX` is accepted by `Kernel.isDefEq` in the isolated pair probe; this is a tiny control, not the expensive `hb` root.

Stored outer head: `Site` / `AlgebraicGeometry.Scheme.ProEt`.

Kernel hints: `regular:20` / `regular:19`.

Why currently cheap: The ordinary mode matcher reduces directly to the `ProEt` branch when the comparison is isolated.

Puncture operation: Expose the named body with `unfold Site`, use a concrete `simp`/`rw`, or independently reconstruct the category provider.

Re-exposure result: The diagnostic body exposure moves the first difference to `Scheme.instCategoryProEt` versus `instCategorySite`; it does not provide a same-root cost replay. Status: **fragile**.

Boundary: `B-HB-TRANSPORT`

Boundary kind: Whole-proposition theorem/transport boundary.

Current fast conversion: `hb := fun M => by transport_exact h M` checks the same helper application in about 4.40--4.80 s under the 400,000-heartbeat diagnostic, with 19,783 calls in the threshold-zero instrumentation.

Stored outer head: The transported argument has exactly the instantiated expected proposition.

Kernel hints: No relevant imported hint changes; the proof proposition is changed by construction.

Why currently cheap: The dependent domain conversion is removed before Kernel comparison.

Puncture operation: Replace the transported premise with the original concrete `h`, or rewrite the concrete goal into component equalities.

Re-exposure result: Restored original root reproduces 239,340,712 calls and the minute-scale comparison. Status: **fragile**.

Boundary: `B-ABSTRACT-HELPER`

Boundary kind: Explicit generic helper parameters for functors, equivalences, and adjunction data.

Current fast conversion: The abstracted helper/After proof checks in about 4.10 s; its expected binder is syntactically aligned with the transported proposition.

Stored outer head: `transport_from_unit` and `mate_transport_abstract` are named declarations with explicit data parameters.

Kernel hints: Imported regular/opaque metadata is unchanged by the local probe; full helper dump is intentionally omitted because it is very large.

Why currently cheap: Concrete sheaf functors are kept outside the dependent proposition comparison.

Puncture operation: Inline concrete functors/equivalences or reconstruct their category instances in the declared dependent type.

Re-exposure result: The original direct specialization re-enters the large `hb` tree. Status: **fragile**.

## 7. CONTROL RESULTS

Original: Reduced-budget direct application times out deterministically around 88--89 s; the 4,000,000-heartbeat diagnostic completes in 577--813 s depending on instrumentation. The READY4.2 counters root is the authoritative provenance run.

Perturbed elaboration: No valid T1/T2/T3 transparency perturbation changed a concrete assignment. The `unif_hint` audit changed the elaboration environment only; normalized S2 pair and full kernel counters remained unchanged.

Frozen replay: Not claimed. There are no two distinct elaborated expressions with the same root obligation to replay; the existing matched composite probe changes the obligation and is diagnostic only.

Kernel-metadata control: Not isolated. `Site` and `ProEt` hints are observed (`regular:20` and `regular:19`), but no same-Expr/different-hint replay was constructed.

Same root obligation preserved?: Whole-`hb` transport preserves the surrounding consumer and dependent telescope but changes the argument proposition. The descendant-alignment attempt did not preserve the original M0 root and is not claimed as a selective control.

What changed: The fast transport control changes the exact proof argument type to the helper's expected instantiated proposition; the restored probe reinstates the original concrete proposition.

## 8. CONCLUSION

Earliest divergence stage: **S0**, retained through S1, S2, and imported S3/S4.

Most likely origin: **source/API-authored dependent representation**, with imported helper declarations freezing the generic `Site` vocabulary. Kernel reduction exposes the mode matcher and category-instance continuation.

Elaborator contribution: **not observed**. The isolated S2 snapshot and unification-hint audit do not show a changed assignment or final expression; timing differences alone are not attributed to elaboration.

Kernel contribution: **confirmed as exposure and amplification**. The M0 dependent proposition comparison expands into the measured M1 continuation and M2 reduction cascade. Whole-proposition transport removes the tree; restoration recreates it.

Current cheap-but-fragile boundaries: `Site` regular definition, whole-`hb` transport, and explicit abstract helper functor/equivalence parameters.

What remains uncertain: the exclusive contribution of the Site delta versus the category-instance path, whether any hidden elaborator assignment occurs in the full theorem application, and a valid same-root frozen replay or metadata-only control.

## Audit note and Batch 2 boundary test

The S0 claim is supported by the written `Scheme.ProEt`/mode-indexed `Site`
interface and confirmed by the isolated S2 `root/fn` pair. The imported S3
snapshot is observational, so finalization is only excluded as the *earliest*
origin; it was not compared against a captured pre-finalization value. No
Elaborator-selected divergence is demonstrated by the unchanged unification
hint replay. E3 puncture: replace the type-correct transported whole-`hb`
premise with the original concrete `h` in the same helper application. The
saved restoration reproduces 239,340,712 calls; the transported version has
19,783 threshold-zero calls. This tests the whole-proposition boundary, not
the isolated `Site` definition's cost.
