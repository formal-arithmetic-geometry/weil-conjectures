# FiniteBaseChangeRestrictionMateTransport head audit

## Case and conversion

- Case ID: `FiniteBaseChangeRestrictionMateTransport`; conversion ID: `FB-hb-49-v1`.
- Declaration: `finite_base_change_restriction_mate_transport`, from `0676f555de6`; module `Algebra/Homology/OpenTensorNormalization/OpenTensorNormalizationData`.
- Lean/Mathlib: 4.35.0; baseline `Before.lean`, dataset revision `7118b5fe0097`.
- Site: application argument 49 (`hb`) of the private `transport_from_unit` helper. The preceding 48 actual arguments include eight category types, their category instances, four equivalences, adjunctions, functors, isomorphisms, and the `hγ` mate proof. The helper's expected Pi domain was reconstructed after substituting all of them.
- Original elaborated expressions preserved: **yes**. `probes/HeadAudit.lean` extracts the original theorem premise `h` and compares its inferred type with the exact binder domain from the diagnostic `NoHB` application. The typed placeholder permits inspecting this pair without paying for the original Kernel check; it is never counted as a proof. Normal Kernel checking is enabled in every timed result.
- Actual expression: `forall M : FiniteModules A X', Eq ...`, the supplied concrete right-square proof.
- Expected expression: `forall M : FiniteModules A X', Eq ...`, the same square instantiated through the helper's abstract categories, functors, and equivalences.
- Canonical Before (4,000,000 heartbeats): 577.08 s wall; After: 4.10 s. Reduced 400,000-heartbeat Before: 88.46 s and deterministic Kernel timeout; `NoHB`: 4.70 s. An isolated Kernel heartbeat count, CPU split, and peak RSS for these prior runs were not retained.

## Head audit

Both sides are `Expr.forallE`, with matching `FiniteModules` binder domains. Their bodies are `Expr.app` applications of `Eq`, each with a `Quiver.Hom` type and two composition sides. The first divergence in the equality type follows `Quiver.Hom` argument 1, then `ProjectionRestriction.Mod` argument 1:

| Side | First divergent head | Universe/arguments | Hint | Immediate body |
|---|---|---|---|---|
| Actual | `Scheme.ProEt` | `.{u}`, one scheme argument | regular definition, height 19 | a Pro-étale site construction |
| Expected | `OpenTensorNormalization.Site` | `.{u}`, mode and scheme arguments | regular definition, height 20 | `match mode with .ordinary => X.ProEt | .systems => ℕ × X.ProEt` |

The `Mod` and `Quiver.Hom` heads themselves agree; the differing site is an implicit/dependent type argument inside the morphism domain. This mismatch repeats in the two sides of the equation. The `Site` body has an immediate matcher; one delta step exposes it, and `.ordinary` can then reduce by iota. The 4.35.0 regular-height rule predicts considering the height-20 `Site` side before height-19 `ProEt`. This is source-guided, not a Kernel execution trace. There is no `Expr.proj` on the first divergent path; `.app`/`.hom` source notation alone does not establish a projection trigger.

## Hypothesis tests

| Hypothesis | Status | Experiment and measurement |
|---|---|---|
| H1: hint/order | **Tested; plausible secondary contributor.** | H1.3 inspects both regular hints and the one-step `Site` body. The greater expected height predicts `Site` unfolding first. The transport control changes the argument representation, not the imported hints, so hint order is not isolated as the cause. |
| H2: same regular head argument | **Not applicable at the initial divergence.** | The aligned outer `Eq` is inductive and `Mod` is an abbrev; the first different regular heads are `ProEt` and `Site`, not a same-regular-head application. |
| H3: projection | **Not applicable at the first divergent path.** | The raw path is `forall`/`Eq`/`Quiver.Hom`/`Mod`/site applications. |
| H4: dependent expected domain | **Tested; confirmed.** | H4.1 reconstructs the 49th binder after the actual first 48 arguments. `HeadAudit.lean` finds the site mismatch. `TransportHead.lean` verifies that the transported argument has exactly the instantiated expected proposition. |
| H5: instance paths | **Tested; plausible amplifier.** | H5.1 logs the concrete category, equivalence, functor, and adjunction terms supplied to the helper. Numerous instantiated types are not syntactically equal; no one instance leaf was independently shown to carry the cost. |
| H6: proof proposition conversion | **Tested; confirmed at this application.** | H6.1 compares the proposition types of the original `h` and expected `hb` first. H6.3 replaces only `hb` by `fun M => by transport_exact h M`, keeping the square proof and all other helper arguments. The 400,000-budget application passes in 4.80 s, 4.12 s user + 0.74 s system, 2,291,216 KB RSS. |
| H7: non-delta reduction | **Tested; possible downstream step.** | H7.1 sees no recursor/let/projection at the original head. Source inspection of `Site` shows a mode matcher after one delta step; whether that iota step is costly was not isolated. |
| H8: context/order | **Tested; not supported as the initial cause.** | The original application-only probe takes 577.57 s, close to the 577.08 s full Before. `NoHB` and `TransportHB` both remove the application hotspot in the same context. |

`probes/TransportHB.lean` is a checked one-argument control under the 400,000-heartbeat budget. It ends the surrounding example with diagnostic `sorry`, so its success is limited to the helper application; the complete `After.lean` checks the full theorem. The typed `sorry` in `HeadAudit.lean` is used only to reconstruct the original expected binder, with the actual type taken from the original premise `h`.

## Causal record

- Initial pair: same `forall` and equality skeleton, with a concrete `ProEt` site in the supplied square and the helper's `Site .ordinary` in its expected square.
- Potential high-level route: compare the corresponding `Mod`/`Quiver.Hom` arguments and then the two equality sides.
- Why it fails: the dependent site argument has different regular heads; the expected binder has already incorporated all preceding concrete helper arguments.
- Predicted reduction: unfold the higher-height `Site`, exposing a mode match and then the `ProEt` representation.
- Why costly: the square is embedded in concrete equivalences, functor objects, and module/category instances, so the unresolved dependent argument can expose a large conversion. The original application takes 577 s at the large budget and times out at 400,000 heartbeats.
- Control: one proof-term replacement gives `hb` the exact expected proposition type and reduces the checked application to 4.80 s.
- Verdict: **unfavorable path from a dependent site-representation mismatch**. Unfolding `Site` is necessary for the original representation, while the transported premise avoids that conversion at this application.

## Evidence and confidence

Observed: original and instantiated binder expressions, the `ProEt`/`Site` head difference and hints, the syntactically aligned transported proposition, and the timed original/transport controls. Interpretation: H4 and H6 are **confirmed** for this application; H1, H5, and the precise downstream role of iota remain plausible. Overall evidence level: **confirmed** for the dependent-domain trigger, without claiming an internal Kernel trace.
