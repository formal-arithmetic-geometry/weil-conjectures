# Slow Derived Tensor: round-three internal cost decomposition

## Environment and method

Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, original consumer
`bdab171985a`, regular-alias control `428569e1ce1`. The new observations
use the READY4.2 kernel with only trace/counter additions. Kernel decisions
are unchanged. Every Lean command had a 3600 s timeout; at most two of this
round's Lean jobs ran simultaneously. All recorded comparisons returned
`true`. The root trace, per-layer counters, and per-field counters come from
one run (`R=1190`). Its observer-heavy 243.210 s must not be compared as an
absolute speed with round two's 62.825 s; calls, paths and same-run shares
are the useful comparisons. A separate F6 timing replay used the same pinned
release kernel; its focused call-count trace used the patched kernel.
Expression sizes in probe output are
`sizeWithoutSharing`; trace `left_size_dag/right_size_dag` count shared nodes.

The exact root is the round-two `MonoidalCategoryStruct.tensorObj` field pair.
It has 6,239,530 recursive calls, 173,251.069 ms comparison-exclusive plus
69,958.522 ms reduction-exclusive time, and a `true` result. Its two lambda
Exprs have sizes 60,951/38,555 and are not pointer-identical. The detailed
events are bounded to the selected root and expensive constructor subtree;
the raw event file remains only in scratch. Reduced files in `sdticd/`
preserve the schema, root aggregates and selected events. The pinned
Environment field inventory in `structure-map.jsonl` supplies constructor
parameter counts and field names for sampled structures; the final observer
also emits projection indices. Full expanded `Expr.repr` proved too large for
a useful retained dump and was deleted; selected Expr heads, hashes, types,
sizes and pointer equality are retained instead.

`root-ready2-selected.jsonl` and `root-ready2-anatomy.txt` are the primary
same-run evidence. `root-ready3-aggregates.jsonl`,
`root-ready3-constructors.jsonl`, the three
`root-ready3-projections-part*.jsonl` files, and
`root-ready3-anatomy.txt` contain the separately linked metadata replay.
The projection records are split solely to keep each reduced file below
5 MB. Probe source and compact probe outputs are in the same directory.

A second, separately linked observational build was used only to complete
the generic constructor/projection metadata inventory. Its direct field
replay is `S=1193` (6,267,700 calls, 75.076 s instrumented). It reaches
the same source `uncurry` constructor after an additional source-composition
comparison. The `S` observer's broad `other` layer label does not follow
that constructor, so its constructor child edges, not that label, are used
below. `R` remains the primary READY4.2 cost attribution; the two runs'
absolute times are not pooled.

## Result: source `uncurry` inside an existence type

The original path is `tensorObj` -> object-action `Functor.obj` ->
`curriedTensor_hasLeftDerivedFunctor₂` proof argument -> comparison of its
two proposition types -> `HasLeftDerivedFunctor₂` ->
`HasLeftDerivedFunctor` -> `Functor.uncurry.obj F` -> `Functor.mk` (root call
38, parent 37). Proof irrelevance is entered; the proof bodies are not the
expensive comparison. The uncurried source Functor is a parameter of the
existence proposition, so this is simultaneously a **type-side gateway**
and **source Functor field work**. The root does not reach a selected
`rightKanExtension`, its counit, or the final curried Functor record.

The pinned API confirms `HasLeftDerivedFunctor₂ F W₁ W₂` abbreviates
`HasLeftDerivedFunctor (uncurry.obj F) (W₁.prod W₂)`. The latter carries a
`HasRightKanExtension W.Q (uncurry.obj F)` witness. Separately,
`totalLeftDerived` selects `rightKanExtension (L₁.prod L₂) (uncurry.obj F)`
from a terminal object of `RightExtension`; `leftDerived₂` curries that
chosen Functor. The two localization arguments must not be conflated.

The exact source expressions on both sides have the form
`curriedTensor (HomotopyCategory ...) ⋙
(Functor.whiskeringRight ...).obj (toDerivedMonoidal Qh quasiIso)`.
Their full Exprs differ (sizes 63,631/52,449); their rendered syntax hides
different monoidal instance and quasi-isomorphism/provider terms. The
`uncurry.obj` applications have sizes 99,499/88,345. In the original path,
the expensive constructor has type
`Functor (HomotopyCategory ... × HomotopyCategory ...) (DerivedMonoidal ...)`.
The source product/category arguments are shared; the target category and
its instance differ. The Environment gives `Functor` fields, in order,
`obj`, `map`, `map_id`, `map_comp`. This exact constructor type and its
projection from `uncurry.obj F`, not its proof declaration names, identify
the owner. There is one expensive exposed `Functor.mk` in this root.

### 12.1 Internal-layer cost decomposition

`R` entries are **exclusive sums within the same original root**.
`D` entries are separate direct comparisons: their times are inclusive
diagnostics, overlap one another, and use different observer modes. An
unentered root layer has no independent root cost; a slow direct replay can
still traverse the same source comparison first.

| Layer / exact pair | Calls | Time | Main descendants | Evidence |
| --- | ---: | ---: | --- | --- |
| Source `F_L ≟ F_R` (D) | 28,223 | 0.998 s | `Functor.comp`, hidden instances | Demonstrated |
| Uncurried `U_L ≟ U_R` (D) | 6,239,463 | 62.503 s | `Functor.mk` fields | Demonstrated |
| Uncurried `U` subtree (R) | 6,239,439 | 243.190 s exclusive | `map_comp`, `map` | Demonstrated |
| `HasLeftDerivedFunctor₂` type (R gateway) | 19 self calls | 0.006 s self exclusive | enters `U`; not additive | Demonstrated |
| `HasLeftDerivedFunctor₂` type (D) | 6,239,476 | 62.725 s | same `U` comparison | Demonstrated |
| `HasRightKanExtension` / `HasTerminal` type (D) | 6,239,706 | 68.455 s | compares `U` before extension data | Strongly supported |
| `RightExtension` category (D) | 6,239,695 | 230.795 s | same `U` dependency | Strongly supported |
| Selected terminal object (D) | 6,239,724 | 206.447 s | terminal proof/type -> `RightExtension` -> `U` | Strongly supported |
| Chosen `left` derived Functor (D) | 6,239,724 | 165.376 s | same type-side path | Strongly supported |
| Counit `hom` (D) | 6,239,724 | 203.121 s | same type-side path | Strongly supported |
| Terminality/universality proof type | not separately isolated | not additive | `IsTerminal`; explicit proof checked | Unknown |
| Product-category derived `G_L ≟ G_R` (D) | 6,239,519 | 225.959 s | proof provider type -> `U` | Strongly supported |
| Curried `curry.obj G_L ≟ curry.obj G_R` (D) | 6,239,527 | 170.062 s | same provider type -> `U` | Strongly supported |
| Actual `X₁` outer application (R) | within 71 | within 0.014 s | object-action entry | Strongly supported |
| Actual `X₂` inner application (R) | within 71 | within 0.014 s | object-action entry | Strongly supported |
| Product localization/providers (R) | not separately isolated | no large independent branch observed | hidden source arguments and dependent types | Not observed |

The two object applications were not separated into independent exclusive
totals; their joint `tensorObj_object_application` bucket is 71 calls,
5.988 ms comparison plus 7.878 ms reduction. Root `HasLeftDerivedFunctor`
itself is one call and 0.002 ms. The entire uncurried bucket is
173.242 s comparison plus 69.948 s reduction, 99.992% of root time.
Standalone selected-object comparisons are expensive **because their
dependent types revisit `U`**. They do not establish independent cost in
chosen-object data. No chosen-object/counit body is entered by the root.

### 12.2 Exact `Functor.mk` identity and fields

Root call 38 is produced when call 37 reduces a projection of
`uncurry.obj F`; its `Functor.mk` result type is the source product
Functor above (type sizes 5,809/5,813). Constructor parameters 0-3
precede fields 4-7. All four field pairs are pointer-unequal.

| Occurrence | Result type / identity | Arg 5 | Arg 6 | Arg 7 | Evidence |
| --- | --- | --- | --- | --- | --- |
| `R:38` | `C × C ⥤ H`; source `uncurry.obj F` | `map` | `map_id` | `map_comp` | Demonstrated |
| `S:30` | `(C ⥤ C) ⥤ (C ⥤ H)`; `whiskeringRight.obj (toDerivedMonoidal ...)` | `map` | `map_id` | `map_comp` | Demonstrated |
| `S:28275` | `C × C ⥤ H`; source `uncurry.obj F` | `map` | `map_id` | `map_comp` | Strongly supported |

Here `C` is the historical HomotopyCategory and `H` its DerivedMonoidal
target. The separate `S` occurrence at call 30 is under 2 ms; the source
`uncurry` occurrence is the expensive one.

| Arg / field | Call | Expr head, left/right | DAG sizes | Calls in field | Same-run exclusive total | Inclusive subtree | Evidence |
| --- | ---: | --- | ---: | ---: | ---: | ---: | --- |
| 4 `obj` | 44 | lambda/lambda | 671/471 | 56,018 | 2.077 s | 2.077 s | Demonstrated |
| 5 `map` | 56,062 | lambda/lambda | 775/575 | 1,902,386 | 80.589 s | 80.589 s | Demonstrated |
| 6 `map_id` | 1,958,448 | `Functor.uncurry._proof_2` / same | 641/441 | 84,173 | 4.964 s | 4.964 s | Demonstrated |
| 7 `map_comp` | 2,042,621 | lambda/lambda, `_proof_3` descendant | 707/507 | 4,196,856 | 155.555 s | 155.555 s | Demonstrated |

Field totals are comparison-exclusive plus reduction-exclusive sums in
the same root, not four separate wall clocks. They sum to 243.184 s;
the remaining 0.005 s of the `U` bucket is constructor/parameter work.
The instantiated `map` field type has sizes 170,455/148,023; `map_id`
817,765/705,577; `map_comp` 2,106,645/1,814,933. The `map` path
enters outer Functor mapping, `NatTrans.app`, inner mapping, composition,
and category/Preadditive instance reductions. For example, in this same
run `NatTrans.app` was unfolded 542,714 times (0.561 s of delta time).
These unfold samples are subcosts, not additions to field totals.

In `S`, the exposed `Functor.mk` at call 28,275 has a 74.626 s inclusive
subtree, 99.4% of its 75.076 s root. Its direct children are `obj` 0.571 s,
`map` 22.702 s, `map_id` 1.010 s, and `map_comp` 50.343 s; their field
heads and sizes match the `uncurry` record pattern in `R`. Another exposed
`Functor.mk` at call 30 is the right-hand source-composition factor,
`whiskeringRight.obj (toDerivedMonoidal ...)`, and costs only 1.882 ms.
The constructor type probe identifies that factor as a Functor from
`(HomotopyCategory ⥤ HomotopyCategory)` to
`(HomotopyCategory ⥤ DerivedMonoidal)`. Thus the additional source factor
is not the dominant `Functor.mk` in either traversal. The `S` reduced
metadata includes all 821 retained constructor and 7,229 projection
records, each with Expr sizes and pointer equality. Projection indices and
field names are resolved against the pinned Environment; some generated
class-constructor arguments exceed its direct-field list. Exactly 66 of
the 821 constructor records are left `out_of_range`, not assigned an
invented semantic name. All 7,229 sampled projections have a resolved
field. The `Functor.mk` arguments used for the cost conclusion are fully
resolved.

### 12.3 Proof versus data

| Comparison | Proof irrelevance | Proposition types | Type-side calls/time | Proof-body work | Evidence |
| --- | --- | --- | --- | --- | --- |
| Top `curriedTensor_hasLeftDerivedFunctor₂` witnesses | entered | different Exprs, DefEq | `U` descendant: 6,239,439 / 243.190 s in R | no body comparison observed | Demonstrated |
| `Functor.uncurry` `map_id` | entered in source record | dependent `forall`/equality types differ | 84,173 / 4.964 s field | no body cost established | Strongly supported |
| `Functor.uncurry` `map_comp` | entered in source record | dependent `forall`/equality types differ | 4,196,856 / 155.555 s field | no body cost established | Strongly supported |
| F2: original witness vs `id` of same witness | entered or quick proof handling | exactly same type Expr | direct comparison <1 ms | immaterial | Demonstrated |

The root has 78,836 proof-irrelevance branch entries. Its global
`proposition_ms` statistic is inclusive and overlaps field time, so it
is not used as an additive charge. The source `map_comp` *proof-field
type* is the largest field; the source `map` data field is also material.

### 12.4 Intervention results

All F variants below are **API-level counterfactuals** or standalone
diagnostics; none was shown to preserve the exact M0 root obligation.
Only a valid root-preserving replacement would justify a claim that the
original theorem became faster. `checkWithKernel` accepted the constructed
expressions where indicated.

| Variant | Changed factor | Root obligation / M0 preserved? | Result | Restoration | Evidence |
| --- | --- | --- | --- | --- | --- |
| F1 source alignment | one `F` argument in `HasLeftDerivedFunctor₂` and `uncurry` | no / no | both direct comparisons `true`, 8 ms each; original type was 62.725 s and `U` 62.503 s in separate trace runs | original source arguments restore cost | Demonstrated for direct pair |
| F2 witness replacement | `proofA` vs `id proofA`, identical proposition | no / no | `true`, <1 ms; confirms proof-body insensitivity only | original unequal proposition types remain | Demonstrated |
| F3 shared provider | use `proofA` as the right `totalLeftDerived` provider | no / no | `G` comparison still `true`, 6,239,511 calls / 170.130 s traced; provider sharing alone did not remove `U` type work | original provider restores same path | Demonstrated |
| F4 explicit candidate | `RightExtension.mk` from original selected `G` and counit, with checked universality proof | no / no | candidate and proof kernel-checked; selected vs rebuilt candidate `true` / 2 ms, `left` 1 ms, counit <1 ms, curry <1 ms probe wall | no independent selected extension tested | Demonstrated for reconstruction; Unknown for new choice |
| F5 shared output | compare `G_L` with the same Expr | no / no | `true`, one kernel call / 0.002 ms; 5.064 s probe wall includes overhead | original two outputs restore source comparison | Demonstrated for identity only |
| F6 curry boundary | original `G` and `curry.obj G`; named regular wrapper | no / no | product `G`: 6,239,519 / 225.959 s; curry: 6,239,527 / 170.062 s; regular consumer: 428 calls / 8.075 ms traced | original source mismatch persists | Demonstrated for each direct comparison |

F4 demonstrates that constructing a candidate record from the already
selected data can be cheap to compare. It does **not** demonstrate that
a different terminal choice or its canonical isomorphism is DefEq to the
original. F5 is a shared-Expr boundary test, not a theorem-level
isomorphism or a validated replacement of the original `tensorObj`.
In F6's separate release-kernel timing replay, the standalone `tensorObj`
probe took 142.054 s forward and 88.541 s reverse, whereas the named
regular consumer took 20 ms forward (probe wall). These are different
obligations; the focused patched-kernel regular trace is 428 calls/8.075 ms.

## Decision and remaining limits

**Outcome A, source uncurrying dominates (Demonstrated for this root).**
The largest exclusive subtree is `uncurry F_L ≟ uncurry F_R` inside the
existence proposition type: 6,239,439 calls and 243.190/243.210 s in
the same instrumented run. `map_comp` contributes 155.555 s (64.0% of
root), `map` 80.589 s (33.1%), `map_id` 4.964 s, `obj` 2.077 s. The
existence proposition is the route to this source comparison; its own
non-source nodes add about 0.006 s. The direct `F` comparison is only
about 1 s, while direct `U` and proposition-type comparisons both have
6.24M calls. Thus construction and comparison of the uncurried source
record, especially its dependent proof-field type, is the decisive
amplifier.

The original root's chosen terminal object, counit, curry fields, and
product-localization provider work are **not observed** as independent
expensive branches. Their direct replay totals are **strongly supported**
as repeated source-type work, not as evidence that their own bodies are
cheap in every context. Terminality proof-type cost beyond `U`, exact
independent counit `app`/naturality cost, and an M0-preserving intervention
remain **Unknown**. The M1/M2 trace labels remain provisional: the trace
does not verify every descendant as a reduction image of the original
mismatch. No change to the mathematical API or kernel is proposed by these
measurements alone.
