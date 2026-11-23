# MISMATCH ORIGIN AND BOUNDARY STABILITY REPORT

Case: `OrderedSpectralRawLattices`

Lean / Mathlib revision: Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); reserved current tree `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`; case source snapshot `f4946fdb6b6`.

Declaration / root conversion: `AlgebraicGeometry.ProEtale.small_spectral_raw_lattices`; conversion from the inferred type of `CondensedRing.exists_stratified_lisse_integral_lattice ℓ K p k hpℓ S` to the local `RawStratifiedLattices` goal.

Source snapshot: the local declaration has three `let` values (`A₀`, `B₀`, `a₀`) and the named `RawStratifiedLattices` predicate. Its helper is an imported declaration whose type and value are already elaborated.

## 1. STAGE SNAPSHOTS

S0 source:

- The source writes `Profinite.continuousMapRingObj` twice and the `sheafCompose.map` coefficient map once on the goal side. The helper application is source-authored as `CondensedRing.exists_stratified_lisse_integral_lattice ...`.
- The source makes the R/H/D instance routes available in the original declaration. The successful control scopes `attribute [-instance]` over `IsRegularLocalRing.toIsLocalRing`, `HenselianLocalRing.toIsLocalRing`, and `IsDomain.of_isSimpleRing`.
- No relevant macro or notation difference was found. The relevant distinction is in inferred instance arguments, not source spelling.

S1 macro-expanded:

- The Batch 0 syntax snapshots preserve the same provider term after expansion; no macro introduces the first mismatch. The generic S0/S1 records are in `moe/A-imported.snapshot` and `moe/A-aligned.snapshot`.

S2 elaborated:

- The first relevant provider term is `Semifield.toCommSemiring` on the inferred helper side and `CommRing.toCommSemiring` on the declared goal side. The generic elaborated records show the exact nodes at `root/body/body/arg/fn/fn` and the corresponding provider payloads.
- In the full root, this node is below the first `let` value `Profinite.continuousMapRingObj`, in its topology/spectral-norm argument through `spectralNorm.nontriviallyNormedField` and `IsLocalRing.toNontrivial`. The same path is repeated in the second `let` value. The source head audit confirms the first unequal constructor is in these values, not their types, and not a projection.
- The aligned source control re-elaborates the same local declaration with all three routes removed. Its first and second `continuousMapRingObj` values become syntactically equal; the third `Functor.map` value and final predicate remain different.

S3 finalized:

- No generated proof declaration or proof abstraction was needed to explain the mismatch. The local probe uses the imported helper directly and the relevant difference is data-bearing.
- Imported helper declarations are S3 `finalization-observable-only` under the Batch 0 contract. Pre-finalization terms for the imported helper are unavailable from the `.olean`.

S4 stored `ConstantInfo`:

- `Profinite.continuousMapRingObj`: `def`, `hints=abbrev`.
- `Semifield.toCommSemiring`: `def`, `hints=abbrev`.
- `CommRing.toCommSemiring`: `def`, `hints=regular:1`.
- The local `RawStratifiedLattices` wrapper is a regular definition (the head audit records height 37); its body is a dependent `forall` after unfolding.
- The imported helper's stored type/value therefore freeze its provider path before the current local priority scope is considered. Raw records: `moe/A-imported.snapshot`, `moe/A-aligned.snapshot`.

S5 Kernel root pair:

- Exact pair: inferred helper type with `let A := ...; let B := ...; let a := ...; forall ...` versus declared `let A₀ := ...; let B₀ := ...; let a₀ := ...; RawStratifiedLattices A₀ B₀ a₀ S`.
- The first active mismatch is M0 at the repeated `continuousMapRingObj` provider argument, `Semifield.toCommSemiring` versus `CommRing.toCommSemiring`.
- Original checked root: 40.23 s fresh (earlier 45.73 s), deterministic timeout; type-only/helper-only controls are about 13.9 s. The all-route aligned source control succeeds in 10.11 s fresh (16.91 s in the separate alignment session).

S6 Kernel-exposed descendants:

- READY4.2 root: 18,944,709 calls. M1 is 8,320,909 calls (43.922% of calls, 64.684% of time), M2 is 3,499,646 calls (36.382% of time), and Matched is 7,124,151 calls (0.698% of time); M0 is the root entry.
- The dominant descendant is `root/binder_body[17]` through nested `Exists` and `Quiver.Hom` into `Functor.obj`/`Mod.X`; 23,580 reducible `Functor.obj` reductions were counted in the earlier exact-site diagnostic. This is downstream exposure, not a claim about the internal reduction order.

## 2. FIRST DIVERGENCE

Exact left/right expressions: `Semifield.toCommSemiring` / `CommRing.toCommSemiring`, each applied to the same relevant type argument inside the topology instance argument of `Profinite.continuousMapRingObj`; the value occurs in both the first and second `let` bindings.

Expr path: `root -> first let value -> Profinite.continuousMapRingObj -> topology/spectralNorm/IsLocalRing.toNontrivial argument -> semiring provider`; repeated under the second let value. The generic S2 node path is `root/body/body/arg/fn/fn` for each provider function.

Earliest stage present: S2 for the concrete provider expressions. The route alternatives are source-visible at S0, but the selected concrete terms first exist after local elaboration.

Latent or active: active at S5 as M0; the surrounding locally-free lattice structure and the named predicate are latent until Kernel descent.

M0 / M1 / M2 consequence: M0 enters the conversion at the provider argument; recursive comparison propagates into M1 and M2 descendants under the dependent lattice predicate.

## 3. ORIGIN

Source-authored: the two `continuousMapRingObj` constructions, the named wrapper, and the local/global availability of the R/H/D routes.

Macro-generated: not observed.

Elaborator-selected: concrete inferred provider arguments are visible at S2, but a causal elaborator contribution to the divergence is not demonstrated under MOE section 11. Removing all three routes changes source-level instance availability before re-elaboration; it is not a transparency perturbation with independently identified changed metavariable assignments and frozen replay.

Declaration-finalization-generated: not observed. No proof-only auxiliary or post-elaboration transformation is needed for the first data-bearing mismatch.

Environment/import-frozen: confirmed for the imported helper side. Its stored provider arguments cannot be rewritten by current local priorities.

Kernel-exposed: the dependent `Exists`/`Quiver.Hom`/`Functor.obj` descendants are exposed after the M0 provider mismatch is encountered. The first representation difference is not kernel-created.

Unknown / mixed: mixed provenance overall: source-authored route availability, elaborator-selected provider terms, then imported/frozen helper data.

## 4. ELABORATOR PROVENANCE

Relevant metavariables: the helper application synthesizes ordinary implicit arguments (`Fact ℓ.Prime`, `Field K`, `Algebra ℚ_[ℓ] K`, `FiniteDimensional`, `Fact p.Prime`, `Field k`, `CharP`, scheme classes). The focused trace records those answers, but does not expose a candidate list naming the R/H/D route inside the imported theorem; no `isDefEq.assign` record identifies a separate transparency-driven assignment.

Instance synthesis choices:

- Original local source: R/H/D routes are available; the concrete topology path reaches `Semifield.toCommSemiring` on the helper/inferred side and `CommRing.toCommSemiring` on the goal side.
- Source controls: `IsRegularLocalRing.toIsLocalRing`, `HenselianLocalRing.toIsLocalRing`, and `IsDomain.of_isSimpleRing` are the three competing routes. Removing one or any pair leaves a different provider mismatch; removing all three aligns the first two ring values.
- The source matrix is valid for the same local obligation, but it is not an explicit same-Expr replay because the imported helper's terms are already fixed.

Implicit arguments: the generic S2 snapshots show the `inferInstance` application carrying the exact provider constants. No hidden proof argument is the first mismatch.

Coercions: no relevant `Coe`, `CoeFun`, or `DFunLike` insertion was found at the first mismatch. The third `Functor.map` value has a separate instance difference.

Transparency modes: no concrete Meta transparency constraint was isolated. The trace records instance synthesis but no useful `isDefEq.transparency` assignment for the R/H/D provider. Therefore no T0/T1/T2 transparency claim is made.

Expected types / local context: the provider is expected as the `CommSemiring` component of a concrete ring/topology structure under `spectralNorm.nontriviallyNormedField` and `IsLocalRing.toNontrivial`; the local context also contains `ℓ`, `p`, `k`, `K`, `S`, and the three let bindings.

Evidence that a choice changed the final Expr: the all-route *source availability* control makes both first and second ring-object values syntactically equal and the checked conversion succeeds, while all six one- or two-route controls retain a mismatch and time out. This establishes the importance of the available routes, not an isolated elaborator decision under section 11.

## 5. KERNEL INPUT AND COST

Stored type/value: the helper's imported stored declaration has the expanded quantified lattice predicate; the local goal stores the named `RawStratifiedLattices` wrapper under the same three-let spine.

Kernel reducibility hints: `continuousMapRingObj` and `Semifield.toCommSemiring` are `abbrev`; `CommRing.toCommSemiring` is `regular:1`; the named wrapper is regular (height 37).

Exact root pair: the inferred helper type versus the declared local goal described in S5.

Recursive calls: 18,944,709 on the original READY4.2 root; the aligned control does not enter a comparable large root.

M1/M2/Matched shares: M1 43.922% calls / 64.684% time; M2 36.382% time; Matched 0.698% time.

Relevant comparison path: first and second ring-object values -> topology/spectral-norm instance -> provider mismatch -> dependent `Exists`/`Quiver.Hom` and `Functor.obj` descendants.

## 6. CHEAP-BOUNDARY INVENTORY

Boundary: `continuousMapRingObj` head.

Boundary kind: named `abbrev` data boundary.

Current fast conversion: aligned first/second ring-object values compare syntactically equal; the complete aligned root succeeds in 10.11--16.91 s.

Stored outer head: `Profinite.continuousMapRingObj`; `hints=abbrev`.

Kernel hints: `abbrev`.

Why currently cheap: matching outer heads avoid entering the concrete topology instance path.

Puncture operation: unfold the abbrev, independently reconstruct the provider, or re-enable one R/H/D route.

Re-exposure result: independently inferred route divergence is the original timeout path; any one or two route restorations still time out.

Future API/refactor risk: changing the wrapper to a regular/body-exposed definition, or letting consumers infer a fresh provider, can expose the topology data.

Status: fragile.

Boundary: `RawStratifiedLattices`.

Boundary kind: named regular proposition boundary.

Current fast conversion: after all-route alignment, the third `Functor.map` value and named-versus-expanded predicate still differ, but the checked conversion succeeds.

Stored outer head: regular `RawStratifiedLattices` (height 37), unfolding to a dependent `forall`.

Kernel hints: regular.

Why currently cheap: a common ring-object representation removes the large data-bearing mismatch before the wrapper is exposed.

Puncture operation: unfold the wrapper or replace the whole-side theorem with concrete `simp`/`rw` reconstruction.

Re-exposure result: wrapper exposure alone is not sufficient to restore the timeout in the aligned control; the provider bundle remains the causal boundary.

Future API/refactor risk: expanding the proposition in downstream declarations can combine it with independently inferred ring objects.

Status: fragile but not the primary trigger.

Boundary: three-let spine (`A`, `B`, `a`).

Boundary kind: let-bound data boundary.

Current fast conversion: both sides retain the same three-let skeleton.

Stored outer head: `Expr.letE` at the root.

Kernel hints: not applicable to the let itself; contained heads carry the hints above.

Why currently cheap: the let shape is shared and is not the first divergent constructor.

Puncture operation: zeta-reduce the lets or inline their values.

Re-exposure result: zeta exposure is not independently causal; the same provider mismatch remains underneath, while the aligned control succeeds with the let shape retained.

Future API/refactor risk: inlining ring objects can make concrete instance paths part of every consumer type.

Status: fragile, currently cheap.

Boundary: whole-side helper theorem/application.

Boundary kind: theorem/transport boundary.

Current fast conversion: binding the helper result and checking only its declared type are about 13.9 s; `exact h` at the final conversion is timeout-scale.

Stored outer head: imported theorem constant on the helper side; local named proposition on the goal side.

Kernel hints: imported declaration metadata is environment-frozen; no metadata-only replay was constructed.

Why currently cheap: the helper can be named without converting its expanded type to the local wrapper.

Puncture operation: consume the helper directly with `exact h` against the concrete goal.

Re-exposure result: restores the 40.23--45.73 s timeout path.

Future API/refactor risk: replacing the whole-side transport with direct concrete proof reconstruction reopens the conversion.

Status: fragile and causally relevant.

## 7. CONTROL RESULTS

Original: R/H/D routes available; first provider divergence is `Semifield.toCommSemiring` versus `CommRing.toCommSemiring`; 18,944,709 calls and deterministic timeout.

Perturbed elaboration: all three routes disabled in the local declaration; both first and second ring-object values become syntactically equal; third map/predicate still differ; checked conversion succeeds. Single and pair removals remain timeouts.

Frozen replay: no valid F0/F1 replay. The imported helper's provider terms are frozen, and changing local availability changes the newly elaborated goal or dependent predicate. A synthetic shared-provider replay would not preserve the exact root obligation.

Kernel-metadata control: none. The observed `abbrev`/`regular:1` difference belongs to different provider constants, so it is not a metadata-only control.

Same root obligation preserved?: yes for the R/H/D source availability matrix and complete all-route alignment; the local declaration, consumer, and final conversion site are retained. The provider expressions change by the explicitly scoped source perturbation.

What changed?: instance availability changes the elaborator-selected provider arguments; the all-route control aligns the two data-valued ring objects and removes the large comparison workload.

## 8. CONCLUSION

Earliest divergence stage: S2, after local elaboration selects concrete R/H/D provider paths; route availability is already source-authored at S0.

Most likely origin: mixed source-authored plus elaborator-selected instance bundle, with the helper side subsequently environment/import-frozen.

Elaborator contribution: **plausible, not demonstrated as causal**. S2 contains inferred provider terms, but the all-route control changes source instance availability and has no frozen F0/F1 replay of independently captured assignments.

Kernel contribution: the M0 provider mismatch exposes a wide dependent comparison, producing the measured M1/M2 propagation under `Exists`/`Quiver.Hom`/`Functor.obj`.

Current cheap-but-fragile boundaries: `continuousMapRingObj` abbrev, named `RawStratifiedLattices`, the three-let spine, and the whole-side helper theorem.

What remains uncertain: exact Kernel reduction order, separate cost of the two repeated ring values versus the third map/predicate, pre-finalization terms for the imported helper, and an explicit provider-preserving F0/F1/F2 replay. The full target dump was intentionally not retained because an unrestricted expression dump exceeded the useful bounded snapshot; existing READY4.2 root records provide the authoritative S5/S6 cost data.

## Audit note and Batch 2 boundary test

The previous "demonstrated" label used the all-route alignment source rewrite
as if it were an elaborator-only perturbation. Section 11 requires aligned
S0/S1 with divergent S2, or a targeted perturbation that records changed
assignments/final Expr and frozen cost. Neither is saved here. The imported
helper's S3 record is finalization-observable-only, so it cannot prove S2/S4
identity. E3 puncture: restore any one of the three scoped R/H/D instance
routes in the type-correct all-disabled control. The first/second
`continuousMapRingObj` provider mismatch returns and the checked conversion
times out in the saved route matrix. The changed source instance scope is
explicit; the separate effect of each provider and an F0/F1 replay remain
unisolated.
