# OrderedSpectralRawLattices head audit

## Case and conversion

- Case ID: `OrderedSpectralRawLattices`; conversion ID: `OS-final-exact-v1`.
- Declaration: `AlgebraicGeometry.ProEtale.small_spectral_raw_lattices`, from `f4946fdb6b6`; module `AlgebraicGeometry/Coefficient/OrderedSpectralLattices`.
- Lean/Mathlib: 4.35.0; baseline: `Before.lean`, dataset revision `7118b5fe0097`.
- Site: final inferred-type / declared-type conversion for `CondensedRing.exists_stratified_lisse_integral_lattice ...`. The local context includes coefficient fields, `ℓ`, `p`, `k`, `S`, and the three local `let` bindings for ring objects and the coefficient map.
- Original elaborated expressions preserved: **yes**, before normalization in `probes/HeadAudit.lean`. The target and helper result are both checked as stored, including their concrete instances.
- Baseline: 45.73 s wall, deterministic Kernel timeout, 3,283,804 KB peak RSS. Type-only and application-only controls take 13.91 s. The heartbeat setting is the source default 200,000; a separate Kernel heartbeat count is unavailable.

## Head audit

| Position | Actual | Expected | Alignment |
|---|---|---|---|
| Outer | `Expr.letE A := ...; let B := ...; let a := ...; forall ...` | `Expr.letE A₀ := ...; let B₀ := ...; let a₀ := ...; RawStratifiedLattices ...` | same three-let shape |
| First let value | `Profinite.continuousMapRingObj` (4 args) | same head (4 args) | its topology instance argument differs |
| Instance leaf | `Semifield.toCommSemiring` (abbrev) | `CommRing.toCommSemiring` (regular height 1) | under `IsLocalRing.toNontrivial`, `spectralNorm.nontriviallyNormedField`, and `instTopologicalSpaceSubtype` |
| Second let value | `Profinite.continuousMapRingObj` | same head | the analogous instance path differs |
| Third let value | `Functor.map` | same head | an instance in `sheafCompose` differs |
| Final body | `Expr.forallE` | application of private `RawStratifiedLattices` (9 args, regular height 37) | the wrapper immediately exposes a `forall` on unfolding |

The first two let-bound types are syntactically equal `Sheaf` applications. The first unequal term is in their **values**, not their types or the final predicate. The raw `Expr` confirms that source-level `let` syntax is retained; no projection or recursor is the initial divergent constructor. The first instance leaf has identical universe level `[0]` on both sides. Proof and implicit arguments remain in the larger dependent functor expressions, but the observed first mismatch is a concrete semiring-instance route.

The 4.35.0 Kernel hint policy predicts that an abbrev is considered before a regular definition if these leaf heads are compared, and that the regular `RawStratifiedLattices` body can expose its `forall`. The audit does **not** trace the actual reduction order. One-step source inspection of `RawStratifiedLattices` shows a quantified locally-free lattice predicate; its body contains `Mod`, `condensedRingObj`, and dependent stratum types. The relevant `continuousMapRingObj` wrapper is itself an abbrev around a sheaf construction.

## Hypothesis tests

All runs below use one Lean thread, synchronous elaboration, normal Kernel checking, and the same imports/options. Each named instance control changes only the indicated local instance availability at this theorem; all single and pair failures are target Kernel timeouts. The later unknown-constant error is a consequence of the failed private theorem.

| Variant | Disabled instances | Wall | User + system | Peak RSS KB | Kernel result |
|---|---|---:|---:|---:|---|
| `Before` | none | 45.73 s | not recorded | 3,283,804 | timeout |
| `DisableRegular` | regular-local-ring | 44.93 s | 44.15 + 0.78 s | 3,284,440 | timeout |
| `DisableHenselian` | henselian-local-ring | 45.23 s | 44.37 + 0.85 s | 3,285,356 | timeout |
| `DisableDomain` | simple-ring/domain | 45.43 s | 44.56 + 0.86 s | 3,284,008 | timeout |
| `DisableRegularHenselian` | first two | 45.23 s | 44.30 + 0.88 s | 3,284,080 | timeout |
| `DisableRegularDomain` | first and third | 45.23 s | 44.39 + 0.82 s | 3,283,492 | timeout |
| `DisableHenselianDomain` | last two | 45.53 s | 44.60 + 0.88 s | 3,284,536 | timeout |
| `After` | all three | 13.71 s | 12.90 + 0.81 s | 2,496,640 | success |

`probes/AllDisabledHead.lean` replays the three-instance setting with the original helper and prints the elaborated pair before the final check. Both first and second let values become **syntactically equal**. The third map value and folded final predicate still differ, but the fully checked `After.lean` succeeds. This directly connects the instance setting, expression alignment, and cost change.

| Hypothesis | Status | Experiment and interpretation |
|---|---|---|
| H1: hint asymmetry | **Tested; plausible contributor.** | H1.3 records the abbrev/regular leaf hints and one-step wrapper body. No same-body declaration-kind control changes these imported structure projections; the instance matrix identifies the chosen terms rather than their hint kind as the effective factor. |
| H2: same regular head argument | **Not applicable at the outer head.** | The outer shape is `let`; the first nested matching `continuousMapRingObj` is an abbrev, not a regular head. The differing argument is audited under H5. |
| H3: projection exposure | **Not applicable to the initial pair.** | The raw first divergent path consists of applications and stored instances, with no `Expr.proj`. |
| H4: dependent expected domain | **Not applicable.** | The costly comparison is the final helper result against the goal, not an application binder. |
| H5: instance paths | **Tested; confirmed.** | H5.1 identifies the exact stored leaf; H5.2 changes one available instance at a time, then pairs and all three. Only all three aligns the first two let values and passes. |
| H6: proof irrelevance | **Not supported as the initial trigger.** | The first unequal term is a structure instance inside a topology argument. No differing proposition-proof pair was needed to explain the observed change. |
| H7: non-delta reduction | **Tested; weakened as the primary cause.** | H7.1 finds outer lets. The successful control retains the same let structure, while aligning its first two values, so let syntax alone is insufficient for the timeout. |
| H8: context/order | **Tested; not supported.** | The isolated final-exact probe in `CLASSIFICATION.md` reproduces the timeout, while the helper binding and declared type alone remain cheap. |

## Causal record

- Initial pair: matching three-let skeletons, but the first ring-object values carry different nested instance paths; the final predicate is expanded versus named.
- Potential high-level route: compare the corresponding let values and then unfold `RawStratifiedLattices` to the `forall` predicate.
- Why it fails: a topology-instance argument diverges at `Semifield.toCommSemiring` versus `CommRing.toCommSemiring`, embedded in a concrete spectral-norm instance.
- Predicted reduction: the Kernel can expose the abbrev leaf and the regular predicate wrapper; exactly which step it takes first is unknown.
- Why costly: comparing the unequal concrete topology/functor values may enter the coefficient sheaf and locally-free lattice structure. The observed timeout and existing `Functor.obj` counters corroborate that downstream work, without tracing it.
- Control: disabling all three competing instances aligns both first let values and gives a 13.71 s checked proof. No subset of the three suffices in the tested matrix.
- Verdict: **unfavorable unfolding path caused by concrete instance misalignment**. The predicate wrapper still needs unfolding, but the control shows that its presence alone is cheap.

## Evidence and confidence

Observed: exact raw path to the first instance leaf, all six failed partial controls, the successful full control, and syntactic alignment of the first two let values in that control. Interpretation: H5 is **confirmed**; interaction among the three instance-search choices is necessary in this source setting. The exact internal Kernel reduction sequence and the remaining third-let difference are unresolved. Overall evidence level: **confirmed** for the instance-path trigger.
