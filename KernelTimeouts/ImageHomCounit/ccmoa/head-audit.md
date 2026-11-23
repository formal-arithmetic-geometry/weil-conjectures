# ImageHomCounit head audit

## Case and conversion

- Case ID: `ImageHomCounit`; conversion ID: `IHC-final-exact-v1`.
- Declaration: `AlgebraicGeometry.Etale.IndEtaleMapping.imageHomIso_counit`, from `212f97dd22a`; module `AlgebraicGeometry/IndEtaleMapping/IndEtaleDerivedImageHomCounit`.
- Lean/Mathlib: 4.35.0; baseline `Before.lean`, dataset revision `7118b5fe0097`.
- Site: final inferred-type / declared-type conversion at `exact h`, where `h` is the concrete `conjugateEquiv_counit` application. Context: coefficient ring `A`, scheme `X`, derived objects `K`, `M`, over-object `T`, and their local category/monoidal instances.
- Original elaborated expressions preserved: **yes**, before normalization in `probes/HeadAudit.lean`. Normal Kernel checking is enabled in timed probes.
- Actual and expected: `Eq` propositions over two compositions of the image-Hom counit square. The inferred equality's morphism type uses a raw derived category of étale sheaves; the goal uses the named `DerivedCategoryModule` wrapper.
- Measured baseline: `FinalExact.lean` 54.83 s wall and approximately 7,459,004 KB peak RSS; `HaveApplication.lean` 2.70 s; `After.lean` 2.60 s. The declaration's heartbeat setting is 200,000. A separate Kernel heartbeat count and CPU split for these prior runs are unavailable.

## Head audit

| Side | Outer shape | Universes and arguments | Relevant metadata |
|---|---|---|---|
| Actual | `Expr.app`, `Eq`; its type is `Quiver.Hom`, sides are `CategoryStruct.comp` | `Eq.{u+2}` with three arguments; `Quiver.Hom` has four, `comp` seven | first divergent type child is `DerivedCategory` (regular height 15, universes `[u+1,u+1,u+2]`) |
| Expected | same `Eq`, `Quiver.Hom`, and composition heads | same `Eq` universe/arity | corresponding child is `DerivedCategoryModule` (abbrev, universe `[u]`) |

The type argument and both equality sides diverge at their first derived-category child. This is a type/data argument difference, ahead of any proof argument. The outer heads and universe of `Eq` match, but the morphism-domain arguments do not. The first divergent raw path has ordinary applications; no `Expr.proj`, let, or recursor is present there. A one-step expansion of the abbrev `DerivedCategoryModule A X` exposes `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))`. A further, separate unfolding of the regular `DerivedCategory` definition would expose `HomologicalComplexUpToQuasiIso`; the audit does not normalize that chain.

The Lean 4.35.0 Kernel hint policy predicts considering an abbrev before a regular definition at the nested pair. That is a prediction from stored metadata, not a trace. The actual raw `DerivedCategory` side also carries concrete `instCategoryDerivedCategory` and `HasDerivedCategory.ofIsGrothendieckAbelian` terms; the wrapper side contains `DerivedCategoryModule._proof_1/_proof_2` in the earlier full-expression print. Their exact downstream contribution has not been separated from the wrapper conversion.

## Hypothesis tests

| Hypothesis | Status | Experiment and measurement |
|---|---|---|
| H1: hints and vocabulary | **Tested; inconclusive for hint causality.** | H1.3 records regular height 15 versus abbrev and the immediate wrapper body. `UniformRaw.lean` changes only the source spelling of `K`/`M` to raw `DerivedCategory`: 55.43 s wall, 54.35 s user + 1.09 s system, 7,459,416 KB RSS. `RegularWrapper.lean` uses a same-body local regular wrapper for those variables: 55.73 s, 54.66 + 1.01 s, 7,462,944 KB. `HeadRaw.lean` and `HeadRegular.lean` show that **neither edit changes the expensive elaborated pair**, so these are negative source controls, not an isolated declaration-kind test. |
| H2: same regular head argument | **Not applicable to the first divergent head.** | Shared `Eq` is inductive and `Quiver.Hom` is the enclosing type constructor; the child heads differ. |
| H3: projection exposure | **Not applicable at the first divergence.** | The raw path is `Eq` -> `Quiver.Hom` -> derived-category application; source `.app` notation alone does not show an `Expr.proj`. |
| H4: dependent expected binder | **Not applicable.** | The helper application is cheap; the hotspot is the final inferred-type/goal comparison. |
| H5: instance paths | **Tested; plausible amplifier.** | H5.1 inspects the exact stored terms in `HeadAudit.lean` and the earlier `PrintConversion.lean`. They show distinct category/derived-category proof paths under the wrapper, but no independent one-instance control removes the cost. |
| H6: proof irrelevance | **Not supported at the first divergence.** | Generated `_proof_n` terms occur deeper in the printed category instances; the first unequal child is the derived-category type itself. No proof-body comparison is assumed to cause the cost. |
| H7: non-delta reduction | **Not supported as the initial trigger.** | H7.1 finds two definition heads, not a lambda/let/recursor/projection at the divergent expression. Later reductions after delta are untraced. |
| H8: context/order | **Tested; not supported.** | The isolated final-exact probe takes 54.83 s and the full Before 55.53 s; the helper binding alone takes 2.70 s. No same-pair context sensitivity was observed. |

The raw-type and regular-wrapper probes are complete, normally Kernel-checked examples. Their first divergent elaborated heads remain exactly the original ones, so their equal timings do not refute a hint effect at the original pair. The fixed `After.lean` uses the wrapper-level `imageHomIso_counit` theorem directly and checks the full obligation, but it changes the proof source rather than one factor of the original conversion; its speed is not counted as an isolation of the internal reduction order.

## Causal record

- Initial pair: two `Eq` propositions with matching outer heads and distinct raw/wrapper derived-category arguments in their morphism types and both composition sides.
- Potential high-level route: compare corresponding `Quiver.Hom` and composition arguments.
- Why it fails: `DerivedCategory (Sheaf ...)` and `DerivedCategoryModule A ...` are different stored heads at the first category argument.
- Predicted reduction: consider the abbrev wrapper first, exposing the raw derived category; further comparison may enter the concrete category and sheaf instance terms.
- Why expensive: the original fully checked final conversion takes about 55 s and 7.46 GB RSS, with large downstream `Functor.obj`/`Add.add` unfold counts in the prior diagnostic. The exact expensive subterm after the wrapper expansion remains unknown.
- Control: changing only the variable type spelling does not alter the pair or cost. The direct wrapper-level theorem avoids this conversion and is fast, but is a different proof construction.
- Verdict: **necessary unfolding for the original raw/wrapper representation**; the reason the subsequent comparison reaches 55 s is unresolved.

## Evidence and confidence

Observed: raw expression pair, Kernel hints, one-step source body, two unchanged-pair negative controls, and timed original/fixed proofs. Interpretation: the need to expose the wrapper is **strongly supported**; H5 as a downstream amplifier is **plausible**. No controlled variant isolates the post-unfold cost. Overall evidence level: **plausible** for the full causal explanation, with a confirmed conversion site.
