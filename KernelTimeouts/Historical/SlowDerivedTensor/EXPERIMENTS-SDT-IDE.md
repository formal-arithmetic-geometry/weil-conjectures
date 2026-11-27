# Slow Derived Tensor, round 11: reduction asymmetry and monoidal instance representation

## 7.1 Executive summary

**Direct child replay:** At the original dependent `Eq` body, the checked provider follows the `DerivedCategory` construction and the stored provider follows `DerivedMonoidal.instMonoidalCategory`. Value WHNF of both reaches `MonoidalCategoryStruct.mk`, but its bodies differ: the checked body contains 58 complete `MC-K-canonical` applications and no complete `MC-K-shortcut` application; the stored body has the reverse counts. The bodies are structurally unequal and Kernel DefEq. The wrapper `DerivedMonoidal L W := D` is definitionally trivial; the instance provider construction accounts for the observed representation difference (**API-level counterfactual**, R3). WHNF exposes a constructor without normalizing its nested fields (**inference** from R2 and implementation audit).

**Direct original-root and reduction-event evidence:** In root 557, projection of `Functor.proj` requests a nested `tensorObj` comparison (call 68). Checked canonical unfolds first (event 181); stored shortcut unfolds at event 183; its body subsequently exposes and unfolds canonical at event 184. The recorded operation is ordinary kernel `whnf` within a projection-triggered child, not the later `lazy_delta` branch. The exact value/type status of that inner call is **unknown**. The event sits below a `proposition_type` ancestor, which does not settle that status.

**Unknown:** There is no pair of complete shortcut applications in the two original unreduced `Eq` bodies, contrary to the round-9b premise. Consequently their eight arguments cannot be compared pairwise. The `regular(24)` versus `regular(25)` hints affect a synthetic equal-body control, but their causal contribution in this root has not been isolated.

## 7.2 Environment and exact source expressions

Pinned revisions verified in isolated scratch: Lean `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1), Mathlib `0df444a360eaa60ab8c11cda51a86af692955474`, consumer `bdab171985a5e6c6e44fc3920386b89fc5627ca3` (**direct source/declaration audit**). The historical READY4.2 kernel and its associated shared library were used for all reported uninstrumented results; the instrumented kernel was rebuilt from the same pinned source with only observational logging.

The root replay is the Kernel comparison of the checked type of `icd_tensorObj_probe` against its stored type, after opening the original twelve-binder context, in `ide-root.lean`. The obligation is `@tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L = @tensorObj (DerivedMonoidal DerivedCategory.Qh (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))) _ inferInstance K L`. The context contains `A`, its category/abelian/Grothendieck/monoidal/preadditive/symmetric/closed/flat-resolution instances, `X`, and `K L`; exact source is retained. The extracted checked and stored provider terms are the third arguments of the two `tensorObj` applications in the dependent `Eq` body. Their full `Expr` dumps are in `stages-ready.out` at `S0.checked` and `S0.stored`; their heads are both elaborated `inferInstance` applications, with sizes 1,785 and 11,973 and different argument spines (**direct child replay**). These are expressions already elaborated into the theorem; reduction does not rerun instance synthesis.

Source locations (**direct source/declaration audit**): `WeilConjectures/FromJoel/CategoryTheory/Monoidal/Derived.lean:35,39` defines `DerivedMonoidal` and `toDerivedMonoidal`; `:144` is the generic `curriedTensor_hasLeftDerivedFunctor₂` field and `:270` the `D'` instance. `WeilConjectures/CategoryTheory/Monoidal/Instances/DerivedCategory.lean:34` is the `D` adapter; `WeilConjectures/FromJoel/Algebra/Homology/DerivedCategory/Monoidal.lean` supplies its underlying instance. `WeilConjectures/CategoryTheory/Monoidal/Instances/HomotopyCategory.lean:28` defines the shortcut; `WeilConjectures/FromJoel/Algebra/Homology/HomotopyCategory/Monoidal.lean:235` defines canonical. The consumer module is `WeilConjectures/SixFunctors/Etale/Derived/Tensor.lean`.

## 7.3 Instance and provider provenance

```text
MC-D  -> DerivedCategory adapter -> generic D instance -> MC-K-canonical in value WHNF
MC-D' -> DerivedMonoidal.ofBifunctor -> previously elaborated generic field
      -> MC-K-shortcut argument -> compiled shortcut body -> MC-K-canonical
```

The first structural difference is in the S0 provider spines. The first complete K shortcut is already present in stored S0, while checked S0 has none. At S2 value WHNF, the first directly comparable constructor bodies expose canonical versus shortcut at corresponding paths (for example `root/fn/fn/fn/fn/fn/fn/fn/arg/body/body/fn/arg/fn/arg/fn/fn/fn/fn/fn/arg`). Source and declaration audit show that the generic field is elaborated under a local `[MonoidalCategory C]`; a concrete shortcut is supplied later. The shortcut's compiled body contains the canonical instance. The arrows through adapter and `ofBifunctor` are declaration applications/reductions; the generic field is an already elaborated application; shortcut-to-canonical is delta followed by beta exposure, with no new synthesis (**direct source/declaration audit**, **direct reduction-event evidence**).

## 7.4 R1: exact shortcut applications

`ide-r1.lean` searches complete eight-argument applications throughout both exact unreduced dependent `Eq` bodies. It finds **zero checked and one stored**; the stored path is `root/arg/fn/fn/arg/arg/arg/fn/fn/fn/fn/fn/arg`, head `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures`, levels `[u + 1, max (u + 1) u']`, hash `3378993285`, size 311, result-type hash `347540801` and size 685. `ide-r1b.lean` follows twelve explicit checked-provider unfold steps through the `DerivedCategory` adapter, its instance, `DerivedMonoidal.instMonoidalCategory`, `ofBifunctor`, and `MonoidalCategoryStruct.mk`; no complete checked shortcut occurs. Hashes identify expressions only within their replay (**direct child replay**).

| Item | Checked | Stored head and inferred type | Structural / DefEq pair |
|---|---|---|---|
| Universe levels | no complete application | `[u + 1, max (u + 1) u']` | unavailable |
| Argument 0 | absent | `CategoryTheory.Sheaf` : `Sort` | unavailable |
| Argument 1 | absent | `ObjectProperty.FullSubcategory.category` : `Category` | unavailable |
| Argument 2 | absent | `CategoryTheory.sheafIsAbelian` : `Abelian` | unavailable |
| Argument 3 | absent | `CategoryTheory.Sheaf.instHasColimitsOfSize` : `HasColimitsOfSize` | unavailable |
| Argument 4 | absent | `AlgebraicGeometry.Etale.sheafMonoidalCategory` : `MonoidalCategory` | unavailable |
| Argument 5 | absent | `CategoryTheory.Sheaf.monoidalPreadditive` : `MonoidalPreadditive` | unavailable |
| Argument 6 | absent | `AlgebraicGeometry.Etale.sheafMonoidalClosed` : `MonoidalClosed` | unavailable |
| Argument 7 | absent | `AlgebraicGeometry.Etale.sheafBraidedCategory` : `BraidedCategory` | unavailable |
| Complete application / result type | absent | one application / inferred type in `r1-ready.out` | unavailable |

The stored ordinary arguments and their inferred types, plus the full result type, are dumped in `r1-types-ready.out`. There is no valid argument pair, complete-application pair, or result-type pair to compare; no shared mutable metavariable comparison state was used for such a nonexistent pair. Kernel comparison of the surrounding dependent `Eq` body returned `true`, which does **not** establish pairwise shortcut-argument equality. The graded tensor witness and generated proof arguments therefore cannot be paired at this boundary. The smallest follow-up is to capture a later, explicitly identified comparison where both sides have complete shortcut applications, if one occurs; do not manufacture one by substituting a provider (**unknown**).

## 7.5 R2: staged reduction

`ide-stages.lean` records hash, size, head, inferred-type head, levels, occurrence counts and paths for each checkpoint. The complete structured records and full S0 dumps are in `stages-ready.out`. Structural/DefEq checks below use the same replay, not cross-run hashes (**direct child replay**).

| Checkpoint / operation | Checked | Stored | Comparison |
|---|---|---|---|
| S0, none | `inferInstance`, size 1,785; shortcut 0, canonical 0 | `inferInstance`, size 11,973; shortcut 1 at `root/arg/arg/fn/fn/fn/fn/fn/arg`, canonical 0 | structurally different provider spines; Kernel DefEq of enclosing body true |
| S1, type WHNF | `MonoidalCategoryStruct`, size 489 | `MonoidalCategoryStruct`, size 3,757 | structural false, Kernel DefEq true; value representation still unresolved |
| S2, value WHNF | `MonoidalCategoryStruct.mk`, size 1,753,267; canonical 58, shortcut 0 | same constructor, size 1,103,755; canonical 0, shortcut 58 | structural false, Kernel DefEq true |
| S3 `tensorObj`, unreduced projection / extracted field / projection WHNF | 0/2/6 canonical | 0/2/6 shortcut | extracted fields structural false, Kernel DefEq true |
| S3 `whiskerLeft`, same sequence | 0/2/14 canonical | 0/2/14 shortcut | structural false, Kernel DefEq true |
| S3 `whiskerRight`, same sequence | 0/6/1 canonical | 0/6/1 shortcut | structural false, Kernel DefEq true |

The S3 `field-whnf` result is also logged separately, alongside each projection's Kernel check. The first concrete shortcut occurrence is stored S0. The first *canonical-versus-shortcut* constructor representation is S2, before field WHNF. The original-root *executed* nested exposure is a later projection at calls 67–68 (R4/R6). S4 provenance is in 7.3; S5 occurrence paths are in the retained snapshot records. This separates type WHNF, value WHNF, projection, and subsequent field WHNF. No full normalization was used as the primary experiment.

## 7.6 R3: provider crossover

The expressions reuse the extracted local context and substitute only `P_D` or `P_D'` in provider positions. Each constructed provider passed `Kernel.check`; target types are definitionally compatible, though structurally different in mixed cells. No explicit cast or transport was inserted. These are **API-level counterfactuals**, not preserved copies of the original theorem obligation.

| Cell | Checked / stored | Kernel check | Value WHNF K representation | Structural / Kernel DefEq |
|---|---|---|---|---|
| A | D / D | both pass | canonical 58 / canonical 58 | true / true |
| B | D' / D' | both pass | shortcut 58 / shortcut 58 | true / true |
| C | D / D' | both pass | canonical 58 / shortcut 58 | false / true |
| D | D' / D | both pass | shortcut 58 / canonical 58 | false / true |

Each WHNF head is `MonoidalCategoryStruct.mk`. The first K occurrences in each arm use the S2 path above; corresponding `tensorObj`, `whiskerLeft`, and `whiskerRight` field representations follow the provider (S3), since the same extracted provider terms are reused. Thus representation follows provider construction rather than comparison position (**API-level counterfactual**). This does not rule out different instantiated arguments within a different, later comparison.

## 7.7 R4: actual delta events

The pinned implementation audit found separate Meta functions `isDefEqDeltaStep` (`Lean/Meta/ExprDefEq.lean:2042`), `isDefEqProjDelta` (`:2080`), and `whnfCoreAtDefEq` (`:2277`). The original replay calls Kernel C++ `type_checker.cpp`; relevant paths are `unfold_definition`, `whnf`, `lazy_delta_reduction_step`, and `lazy_delta_proj_reduction`. The instrumentation records the actual argument and return of `unfold_definition`, tagged by caller and side, with event sequence, root/call/parent IDs, depth, head, hints, before/after expressions and hashes, transparency and projection metadata. `expression_type` is `not-sampled`; `comparison_context` is `unknown`; expression text is capped at 4,096 characters (**Lean implementation audit**).

| Event | Root/call/parent | Side, operation, head | What happened |
|---|---|---|---|
| 13–14 | 557/6/2 | checked then stored, `lazy_delta`, `tensorObj` | first provider-facing delta steps |
| 15–22 | 557/6/2 | ordinary `whnf` | checked `toMonoidalCategoryStruct` and D adapter chain; stored `toMonoidalCategoryStruct` and D' instance |
| 181 | 557/68/67 | checked, `whnf`, canonical, `regular(24)` | canonical application unfolds first |
| 183 | 557/68/67 | stored, `whnf`, shortcut, `regular(25)` | actual shortcut application unfolds to its compiled lambda/body |
| 184 | 557/68/67 | stored, `whnf`, canonical, `regular(24)` | canonical application exposed by that body unfolds |

Call chain: root 1 -> dependent `Eq` body 2 -> `tensorObj` argument 6 -> `Functor.obj` 7 -> ... -> `Quotient.as` 66 -> `Functor.proj` projection 67 -> nested `tensorObj` second-WHNF child 68. At call 67 a `projection_whnf` event changes both heads from `Functor.proj` to `tensorObj`; call 68 then performs the sequence above. The first actual stored shortcut delta is **event 183**, confirmed as the first shortcut-head event in the complete raw log, not the later canonical-versus-shortcut comparison identified in round 10. Serialized before/after expression prefixes (capped at 4,096 characters), hashes, and exact event IDs are retained in `r4-focused.jsonl` (**direct original-root evidence**, **direct reduction-event evidence**). A `proposition_type` ancestor exists, but the inner value/type/proposition classification is **unknown**. Events 181 and 183 have different heads and hints; this trace alone cannot assign cause to the hint difference.

## 7.8 R5: transparency and hints

R5-A uses the extracted provider and saved/restored Meta state for each DefEq check. The provider observations are **direct child replay**; Meta DefEq here is not the Kernel root check.

| Transparency | Checked provider WHNF | Stored provider WHNF | K applications in providers | Meta DefEq |
|---|---|---|---|---|
| reducible | `toMonoidalCategoryStruct` | `toMonoidalCategoryStruct` | 0 canonical / 1 shortcut | false |
| instances | D `_aux_1` | `MonoidalCategory` projection | 0 canonical / 1 shortcut | false |
| default | `MonoidalCategoryStruct.mk` | same constructor | 58 canonical / 58 shortcut | true |
| all | `MonoidalCategoryStruct.mk` | same constructor | 58 canonical / 58 shortcut | true |

The supplementary `r5a-ready.out` replay measures all three projected fields under each mode. At `.reducible` and `.instances`, `tensorObj`, `whiskerLeft`, and `whiskerRight` all remain projection heads, with zero canonical occurrences on checked and one embedded shortcut on stored; each pair is structurally unequal. At `.default` and `.all`, their WHNFs have respectively 6, 14, and 1 canonical occurrences on checked and the same counts of shortcuts on stored, again structurally unequal. The first two WHNF heads are lambdas; `whiskerRight` reaches `Quotient.mk`. The provider asymmetry persists at `.default` and `.all`; exposing a shared constructor does not make its nested expressions structurally identical (**direct child replay**).

R5-B creates four disposable, Kernel-checked `Nat` definitions with the same body `7`, using the pinned declaration API to assign `.regular 24` and `.regular 25`. All four comparison controls return Kernel DefEq true (**API-level counterfactual**, **direct reduction-event evidence**).

| Control | Checked / stored hint | First actual delta | Result |
|---|---|---|---|
| original relative order | 24 / 25 | stored 25, then checked 24 | DefEq true |
| equal 25 | 25 / 25 | checked, then stored | DefEq true |
| swapped | 25 / 24 | checked 25, then stored 24 | DefEq true |
| equal 24 | 24 / 24 | checked, then stored | DefEq true |

The synthetic control establishes a reduction-order effect of hints for equal-body definitions. It has no monoidal provider representation to inspect, so that requested outcome remains **unknown** for the actual providers. It does not prove a causal role of those two hints in the real provider asymmetry (**unknown**). The root's parent projection and different provider bodies are competing influences.

## 7.9 R6: original-root integration

The uninstrumented READY4.2 and instrumented replays use the same `ide-root.lean` obligation and exact local context. Both return Kernel DefEq `true`, root 557, 6,239,533 successful recursive calls, no failures, and maximum depth 95. Uninstrumented trace wall 59,953 ms, command wall 64,161 ms; instrumented trace wall 64,323 ms, command wall 68,516 ms. The 7.3% trace-wall difference is logging/build overhead, not an attribution to a reduction branch. The provider events and projection-triggered events 181/183/184 occur in this original-root replay (**direct original-root evidence**, **direct reduction-event evidence**). The separate S0–S3 probes reproduce the same provider representation pattern but do not themselves establish an event in the original root.

## 7.10 Causal conclusion

| Hypothesis | Evaluation and evidence |
|---|---|
| H1: demand-driven nested fields | Supported: S2 reaches a constructor while retaining 58 unexpanded K applications on each side; later projection requests deeper reduction (**direct child replay**, **Lean implementation audit**). |
| H2: provider construction path | Supported: all four Kernel-checked crossovers follow D or D' regardless of checked/stored position (**API-level counterfactual**). |
| H3: lazy delta and projection policy | Supported as an exposure mechanism: `lazy_delta` opens outer `tensorObj` at call 6; projection at call 67 requests nested `whnf` and event 183. The precise policy contribution to side selection is unisolated (**direct reduction-event evidence**, **unknown**). |
| H4: shortcut arguments/universes/proofs | Unresolved: only stored has a complete original unreduced shortcut application, so exact pairwise comparison is impossible there (**direct child replay**, **unknown**). |
| H5: value/type context dependence | Unresolved: event schema has no reliable inner comparison classification; its proposition-type ancestor is insufficient (**direct reduction-event evidence**, **unknown**). |

The verified mechanism is elaborated provider provenance plus demand-driven WHNF: the two definitionally equal category types retain different monoidal instance expressions; WHNF exposes a common structure constructor without recursively replacing the nested shortcut; a later projection requests the nested WHNF that unfolds the shortcut's compiled body into canonical. DefEq succeeds without requiring structural identity (**inference** grounded in R2–R4).

## 7.11 Remaining unknowns and next experiments

1. **Unknown:** exact argument-by-argument equality of two original shortcut applications. No checked application exists at the measured boundary. Capture the earliest later call where two complete shortcut applications coexist; if none exists, record non-applicability permanently.
2. **Unknown:** whether event 183 is in a value, field dependent-type, or proposition-type comparison. Add an observational context stack around Kernel `infer_type`, proof irrelevance, and recursive `is_def_eq`, then replay root 557.
3. **Unknown:** causal effect of `regular(24/25)` on this specific root. Rebuild disposable pinned declarations with equalized/swapped hints while preserving both provider bodies and rerun the same extracted comparison; the synthetic `Nat` control does not substitute for that intervention.
4. **Unknown:** the full untruncated before/after expressions for event 183. Add an event-ID-targeted formatter with a larger bound and replay root 557; current event prefixes and hashes establish the head transition but do not preserve every argument of its expanded body.

## 7.12 Reproducibility and artifact manifest

`sdtide/` contains `ide-r1.lean`, `ide-r1b.lean`, `ide-stages.lean`, `ide-r5a.lean`, `ide-hints.lean`, `ide-root.lean`; `instrumentation.patch`; `r1-ready.out`, `r1-types-ready.out`, `r1b-ready.out`, `stages-ready.out`, `r5a-ready.out`, `hints-instrumented.out`; `r4-focused.jsonl`, `hints-events.jsonl`; and both root `.out`/`.err` pairs. `stages-ready.out` contains full S0 expression dumps and structured S0–S3/R3/R5 records. `r4-focused.jsonl` retains relevant actual before/after expression prefixes and parent events. Raw trace remains only in scratch (133 MiB); no raw trace exceeds 2 GB. All retained files are under 5 MB.

Run in the isolated consumer copy with `timeout 3600`, zero Lean heartbeats (`set_option maxHeartbeats 0` in replay probes), and `lake env` plus `LD_LIBRARY_PATH` explicitly pointing at the READY4.2 library before the READY4.2 executable. With `SCRATCH` set to the isolated round directory and `READY` to the historical READY4.2 directory, the invocation pattern is:

```sh
cd "$SCRATCH/hist"
timeout 3600 lake env env LD_LIBRARY_PATH="$READY/lib/lean:$READY/lib:$LD_LIBRARY_PATH" "$READY/bin/lean" ide-stages.lean
LEAN_DEFEQ_ANATOMY=trace LEAN_DEFEQ_MIN_MS=100 timeout 3600 lake env env LD_LIBRARY_PATH="$READY/lib/lean:$READY/lib:$LD_LIBRARY_PATH" "$READY/bin/lean" ide-root.lean
```

Substitute `ide-r1.lean`, `ide-r1b.lean`, or `ide-r5a.lean` for the first command as needed. For the instrumented root, add `LEAN_DEFEQ_MPRWE_ROOT=557 LEAN_DEFEQ_MPRWE_MAX_EVENTS=200000 LEAN_DEFEQ_MPRWE_EVENTS=<scratch-log>` and select the scratch-built instrumented library/executable. The first diagnostic `lake env` replays loaded the standard library because `lake env` prepended its path; their numbers are excluded. The corrected runs are the `*-ready.*` files. `r1-ready`, `r1-types-ready`, `r1b-ready`, `stages-ready`, `hints-instrumented`, and both root replays exited successfully; Kernel checks are listed in R3 and R5. Disk use was 83% after the build, below 90%.

The scratch build initially used `-j8` briefly while a root replay was running, exceeding this round's three-Lean-process ceiling; it was stopped immediately and rebuilt with `-j2`. This is a protocol deviation, disclosed here; the retained measured replays were run with at most one Lean process from this investigation, each under a 3,600-second timeout. No shared checkout, `u9w`, or historical source was edited. The patch adds observational logging only; DefEq result and recursive call count match the uninstrumented root. No commit or push was made.

## 8 Acceptance criteria

| Question | Outcome and evidence label |
|---|---|
| 1. Two shortcut applications equivalent? | Not answerable at unreduced boundary: checked 0, stored 1 (**direct child replay**, **unknown**). |
| 2. First checkpoint exposing different K representations? | Stored shortcut already S0; first canonical/shortcut constructor pair S2 (**direct child replay**). |
| 3. Provider, position, or arguments? | Provider path in four crossovers; argument contribution later remains unknown (**API-level counterfactual**, **unknown**). |
| 4. First relevant shortcut-to-canonical event? | Stored shortcut delta event 183, then canonical event 184 (**direct reduction-event evidence**). |
| 5. Requesting parent? | `Functor.proj` projection call 67 -> nested `tensorObj` WHNF call 68 (**direct original-root evidence**). |
| 6. Value/projection/type? | Projection-triggered `whnf` is established; exact inner value/type classification unknown (**direct reduction-event evidence**, **unknown**). |
| 7. Transparency/hints? | Transparency changes provider WHNF/Meta DefEq; hint ranking changes synthetic reduction order, real-root causal effect unknown (**direct child replay**, **API-level counterfactual**, **unknown**). |
| 8. Original root reproduced? | Yes, same root result/call count and directly captured events (**direct original-root evidence**). |

The strict success criterion is **partially met**, not fully met: questions 1 and 6 lack the specified evidence, and the real-root hint cause is unresolved. The central provenance and executed shortcut unfolding are directly established.
