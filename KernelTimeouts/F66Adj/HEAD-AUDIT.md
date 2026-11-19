# F66Adj head audit

## Case and conversion

- Case ID: `F66Adj`; conversion ID: `F66-hR-39-v1`.
- Declaration: `imageHomIso_naturality`, from `f66ad18a9ed`; module `AlgebraicGeometry/IndEtaleMapping/IndEtaleDerivedImageHomComp`.
- Lean/Mathlib: 4.35.0; baseline `Before.lean`, dataset revision `7118b5fe0097`.
- Site: argument 39 (`hR`) of `homIso_naturality_of_counit`, after the actual preceding 38 category, functor, adjunction, isomorphism, object, morphism, and proof arguments have instantiated the helper's Pi binders. The original argument is `imageRestriction_counit A _ _ (Over.mk f.left)`.
- Original elaborated expressions preserved: **yes**, via `probes/HeadAudit.lean` before normalization. Normal Kernel checking is enabled in timed probes.
- Actual and expected expressions: two `Eq` propositions for the restriction counit square. Their printed mathematical composites look alike, but the stored morphism domains differ as described below.
- Full Before: 116.48 s wall, 12,639,544 KB peak RSS. Application-only baseline: 35.32 s; type-only: 3.10 s; After: 3.40 s. The original theorem uses a 400,000-heartbeat setting; an isolated Kernel heartbeat count and application-only CPU/RSS were not retained in the prior round.

## Head audit

| Side | Outer constructor/head | Universes/arguments | First divergent path |
|---|---|---|---|
| Actual | `Expr.app`, `Eq` | `Eq.{u+2}`, type and two sides | `Eq` type -> `Quiver.Hom` argument 1 -> `DerivedCategoryModule` scheme argument -> `Over.left` of a nested over-object |
| Expected | `Expr.app`, `Eq` | same `Eq` universe and arity | same path ends in the local scheme variable `X` |

The equality sides are `CategoryStruct.comp` applications with seven arguments. They repeat the same first scheme mismatch. `DerivedCategoryModule` has three arguments and an abbrev Kernel hint; its immediate applied body is `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))`. The actual divergent `Over.left` is an abbrev (`.{u,u+1}`, four arguments) whose one-step source body is `Comma.left f`. The expected leaf is a free variable with type `Scheme`. No raw `Expr.proj` occurs on the first divergent path; any field reduction after unfolding `Over.left` is a later possibility, not an observed first step.

The application spine has 41 arguments. Some earlier instantiated types are not syntactically equal, including derived-category instances and concrete functors, but timed prefixes show they are not the first expensive check. The proof argument's **proposition type**, not its proof body, is the audited pair. Because the original `Over.left` application and local `X` have different heads, no direct comparison closes that leaf. The hint policy does not provide a two-definition order for an abbrev versus a free variable; the source predicts that exposing `Over.left`/`Comma.left` is a possible route, without claiming an internal trace.

## Hypothesis tests

| Hypothesis | Status | Experiment and measurement |
|---|---|---|
| H1: hint/order | **Not applicable as a two-head order explanation.** | H1.3 inspects the one-step `Over.left` body, but its counterpart is a free variable, not another definition with a competing hint. |
| H2: same regular head argument | **Not applicable at the initial pair.** | The outer shared head is inductive `Eq`; the first unequal leaf is an abbrev versus a free variable. |
| H3: projection exposure | **Not established.** | H3.1 raw-constructor inspection finds `Expr.app Over.left`, not `Expr.proj`. Source inspection finds `Comma.left` beneath it. A valid unprojected-object control would need objects of the same over-category type; this pair does not provide them. |
| H4: instantiated dependent domain | **Tested; confirmed.** | H4.1 reconstructs binder 39 after arguments 1-38. `HeadAudit.lean` identifies the nested `Over.left` versus local `X`; `ReplaceHRHead.lean` finds a different, cheaper first divergence after changing only the proof argument. |
| H5: concrete instance paths | **Tested; not sufficient for this hotspot.** | H5.1 records the actual instance paths. In the fast replacement pair, the first remaining difference is `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory` (regular height 27) versus `ExternalRHom.siteDerivedMonoidal` (regular height 32), yet the application passes in 3.70 s. |
| H6: proof proposition types | **Tested; confirmed.** | H6.1 compares `imageRestriction_counit`'s inferred `Eq` with the exact expected `hR` binder. The application remains cheap through proof argument 38 and jumps at 39. Replacing only that proof by `restriction_counit A f.left _ _` removes the jump. |
| H7: non-delta reduction | **Not supported as the initial trigger.** | H7.1 sees ordinary applications at the divergent path. A later field reduction under `Over.left` is possible but unmeasured. |
| H8: context/order | **Not supported for argument 39.** | The application-only probe reproduces a 35 s Kernel cost; the full theorem adds a separate final handoff. No same-pair context-only variation was observed. |

The controlled prefix matrix uses the same helper, theorem obligation, imports, and options. Each probe ends with diagnostic `sorry` only **after** the partial helper application; no skipped Kernel result is counted as a proof.

| Probe | Last supplied argument / changed factor | Wall | User + system | Peak RSS KB | Result |
|---|---|---:|---:|---:|---|
| `Prefix28` | isomorphism `c` | 3.10 s | 2.23 + 0.88 s | 2,801,776 | partial application checked |
| `Prefix36` | restriction morphism `R` | 3.10 s | 2.20 + 0.87 s | 2,807,224 | checked |
| `Prefix37` | first counit proof | 3.30 s | 2.33 + 0.90 s | 2,809,668 | checked |
| `Prefix38` | second counit proof | 3.40 s | 2.45 + 0.93 s | 2,813,976 | checked |
| `Prefix39` | original restriction counit proof | 35.22 s | 34.17 + 1.01 s | 5,629,700 | checked, expensive |
| `ReplaceTauQ` | only preceding tensor-isomorphism argument changed | 35.12 s | 34.08 + 0.99 s | 5,631,848 | checked, still expensive |
| `ReplaceHR` | only argument 39 uses `restriction_counit` | 3.70 s | 2.76 + 0.87 s | 2,820,088 | checked, cheap |

`ReplaceHRHead.lean` confirms that the source edit changes the elaborated proposition pair: the nested scheme mismatch is gone, while a different monoidal-instance difference remains. The full `After.lean` includes further helper-interface and final-handoff edits, so its 3.40 s result is evidence for the complete fixed theorem, not an attribution of the full speedup solely to argument 39.

## Causal record

- Initial pair: same `Eq`/`Quiver.Hom`/composition heads, with unequal dependent scheme parameters beneath `DerivedCategoryModule`.
- Potential high-level route: compare the corresponding morphism domains and then the two sides of the counit square.
- Why it fails: the original proof specializes through `Over.mk f.left`, leaving nested `Over.left` in its stored proposition where the helper binder has local `X`.
- Predicted reduction: expose `Over.left` and possibly its `Comma.left` field, then reconcile the concrete derived-category and functor paths. The exact Kernel sequence is unknown.
- Why costly: the mismatch lies inside category and functor objects used by `NatTrans.app`; the application jumps from 3.4 s before argument 39 to 35.2 s with it. Prior diagnostics show large downstream `Functor.obj` and additive unfolds.
- Control: `restriction_counit` supplies the same square through the direct restriction interface; its checked application takes 3.70 s, while the tensor-isomorphism-only edit does not help.
- Verdict: **unfavorable path from the proof proposition's scheme representation**. The control removes that specific expensive conversion without requiring the remaining instance paths to be syntactically identical.

## Evidence and confidence

Observed: raw proposition pair, first divergent leaf, one-argument prefix boundary, negative preceding-argument control, positive proof-argument control, and the fast control's remaining instance difference. Interpretation: H4/H6 are **confirmed** for this application. Projection reduction and the exact downstream Kernel path remain unclassified. Overall evidence level: **confirmed** for the argument-39 representation trigger.
