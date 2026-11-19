# EtaleHomComparisonReversedExact head audit

## Case and conversion

- Case ID: `EtaleHomComparisonReversedExact`; conversion ID: `EH-hv-26-v1`.
- Declaration: `etaleHomComparison_reversedExact_commShift_component`, from `8ca2e912b93`; module `AlgebraicGeometry/Etale/Hom/EtaleHomComparisonModels`.
- Lean/Mathlib: 4.35.0; baseline `Before.lean` at dataset revision `7118b5fe0097`.
- Site: application argument 26 of `derivedTensorHomShiftComparison_component`, the `hv` transpose premise. The expected Pi domain below was reconstructed after substituting the actual first 25 arguments, including the two module categories, their instances, `X`, scalar extension, comm-shift, `M`, and `v`.
- Original elaborated expressions preserved: **yes** in `probes/HeadAudit.lean`, before normalization. Normal Kernel checking is enabled for timed probes.
- Actual inferred type: `IsEtaleHomTranspose X φ M v`.
- Expected binder domain: a `forall K : DerivedCategory (Sheaf ...), ...` transpose equation over the generic tensor-Hom interfaces.
- Baseline application-only check: 29.02 s wall, versus about 3.2 s with Kernel skipped; the full Before handoff takes about 110 s, and After takes about 3.5 s. The heartbeat setting is 200,000. An isolated Kernel heartbeat count and application-only peak RSS were not retained in the prior round.

## Head audit

| Side | Outer constructor/head | Universe and arguments | Declaration hint and one-step body |
|---|---|---|---|
| Actual | `Expr.app`, `IsEtaleHomTranspose` | `.{u}`, eight arguments: coefficient types/instances, `X`, `φ`, `M`, `v` | regular definition, height 34; applied body exposes a `forall K` and a morphism equality |
| Expected | `Expr.forallE` | domain is raw `DerivedCategory (Sheaf ...)`; body is the instantiated transpose equality | binder, no declaration hint |

Application arguments 1-5 and 7-14 have syntactically matching inferred types and instantiated domains in the structural probe. Several later concrete functor/instance types are not syntactically equal, but the prior `NoHV` control shows that only replacing argument 26 removes the application hotspot. The actual `hv` is a proof argument; its proposition type must be converted to the helper's binder domain. The original pair has different constructors, so a direct same-head comparison cannot finish. No `Expr.proj` or recursor is on the first divergent path.

One source-level unfolding of `IsEtaleHomTranspose` exposes a `forall K : DerivedCategoryModule A X` whose body is the evaluation-transpose equation. `probes/ExpandedHead.lean` checks that expanded form in the actual context. Its first divergent child is the quantified domain: `DerivedCategoryModule` (abbrev, universe `[u]`) versus raw `DerivedCategory` (regular height 15, universes `[u+1,u+1,u+2]`). One unfolding of the abbrev exposes `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))`. The 4.35.0 hint policy predicts considering the abbrev side before the regular side at this nested pair; the audit does not observe the actual Kernel step.

## Hypothesis tests

| Hypothesis | Status | Experiment and measurement |
|---|---|---|
| H1: reducibility hints | **Tested; supported as a nested contributor.** | H1.3 inspects the immediate `IsEtaleHomTranspose` and `DerivedCategoryModule` bodies. The expanded premise retains the abbrev/regular domain mismatch and costs 28.72 s. A same-body declaration-kind matrix would require changing imported categories and was not run; hint order is a prediction, not an isolated cause. |
| H2: same regular head argument | **Not applicable to the initial pair.** | The original heads are a regular predicate and a `forall`; after expansion, the mismatch is in binder domains rather than arguments to a shared regular constant. |
| H3: projection exposure | **Not applicable at the initial site.** | The raw first divergent path has applications and a binder, not `Expr.proj`. Source `.app` notation is not treated as proof of a projection. |
| H4: instantiated dependent domain | **Tested; confirmed.** | H4.1 reconstructs binder 26 from the actual preceding 25 arguments. `ExpandedHead.lean` identifies its wrapper/raw quantified-domain difference. Replacing only the supplied `hv` term with `fun K => by transport_exact hv K` makes its inferred proposition syntactically equal to the expected domain in `TransportHead.lean`. |
| H5: instance paths | **Tested; plausible downstream contributor.** | H5.1 inspects concrete instances in the first 25 arguments and the two domain expressions. Their paths are not all syntactically equal, but no single instance leaf was isolated as the trigger. |
| H6: proof proposition types | **Tested; supported.** | H6.1 compares the inferred proposition of `hv`, not its proof body, with the exact expected domain. H6.3 replaces the proof by a transported lambda of the expected type. The application drops from 29.02 s to 3.40 s; the final theorem is checked in `After.lean`. |
| H7: non-delta reduction | **Not supported at the first step.** | H7.1 sees a regular definition versus a binder and then an abbrev versus a regular definition. No initial recursor/let/projection was found; later reductions were not traced. |
| H8: context/order | **Not applicable as a separate trigger.** | The application-only and full Before contain different subsequent conversions. Their 29 s versus 110 s totals do not isolate a cache or check-order effect at argument 26. |

`probes/ExpandedHV.lean` uses the explicit source body of `IsEtaleHomTranspose` as the premise and keeps the rest of the helper application: 28.72 s wall, 27.75 s user + 0.94 s system, 5,480,764 KB RSS. It remains slow because the elaborated quantified domain is still the wrapper. `probes/TransportHV.lean` changes only argument 26, preserves its proposition and all other helper arguments, and takes 3.40 s wall, 2.45 s user + 0.94 s system, 3,162,704 KB RSS. `TransportHead.lean` confirms syntactic equality of the transported proposition type and instantiated binder. These application-only probes finish the surrounding example with diagnostic `sorry`; success is claimed for the checked helper application, while the fully proved `After.lean` supplies the full-theorem control.

## Causal record

- Initial pair: named transpose proposition versus the helper's expanded `forall` domain.
- Potential high-level route: after exposing the predicate, compare corresponding binder domains and equality bodies.
- Why it fails: the actual domain is `DerivedCategoryModule`; the expected domain is raw `DerivedCategory (Sheaf ...)`, with different stored category/instance paths beneath it.
- Predicted reduction: unfold `IsEtaleHomTranspose`, then consider the abbrev wrapper domain. The exact Kernel sequence is not directly observed.
- First exposure: a dependent morphism equality containing scalar extension, tensor-Hom comparison, adjunction counits, and `v.app`.
- Why costly: the remaining wrapper/raw domain mismatch forces comparison under those concrete dependent functor and category structures; the original helper application takes 29 s and has hundreds of thousands of routine downstream unfolds in the prior diagnostics.
- Control: the transported lambda presents the same premise at the exact expected domain and removes the expensive argument check.
- Verdict: **unfavorable path caused by the quantified-domain representation mismatch** after a necessary initial predicate unfolding.

## Evidence and confidence

Observed: actual and instantiated expected types, the expanded-form domain mismatch, the syntactically aligned transported form, and measured 29.02/28.72/3.40 s controls. Interpretation: H4 is **confirmed**; H6 is **strongly supported**; H1 and H5 are plausible contributors to the downstream cost. The precise Kernel reduction order after the first mismatch remains unknown. Overall evidence level: **confirmed** for the domain-alignment cause.
