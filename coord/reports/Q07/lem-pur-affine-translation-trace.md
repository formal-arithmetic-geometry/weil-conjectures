# Stage 1 report: lem-pur-affine-translation-trace

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-affine-translation-trace.json`: statement split into four proof steps; no new nodes; Mathlib searches found no match.
- `citations.json`: 16 verbatim node-statement citations, one for each use in the four steps.
- `searches.jsonl`: all required Mathlib searches, including a second phrasing.

Attachments: none. I searched the read-only slopmaster2 source by item id, key phrases, and blueprint tag; no sorry-free declaration under `WeilConjectures/` states this item exactly. The existing `lem-amb-linear-trace-invariance` is only for invertible linear changes of coordinates, so it is not an attachment or duplicate.

WANTED: none.

The imported item had the correct statement but no proof. I retained its hypotheses and dependencies. The proof follows the current main-20261015 route: universalize the translation over the affine parameter, identify the conjugated normalized trace with multiplication by a locally constant unit, evaluate it at the zero translation, use connected affine fibres to force the unit to be one, and specialize to the given section. The final sentence uses the existing ordinary/pro-etale vector-integration comparison. No statement correction was needed.

## Review by Q07

I read the item node, `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-thm-smooth-purity.json`, the current blueprint's smooth-purity section, the detailed vector-bundle orientation proof (`sk-prop-sp-orientation-vector-bundle.proof.md`), and the existing statements of every cited node. In Step 1 I checked that finite type over the finite field gives the Noetherian hypotheses, that the universal affine-space translation is an automorphism over (P=\mathbf A^d_S), and that `lem-amb-compact-action-base-change` supplies exactly the actual exchange action and its base-change equation. I also checked that `lem-amb-affine-space-top-trace` supplies both trace invertibility and trace base change.

In Step 2 I checked that conjugating by the trace is a degree-zero automorphism, that the cited fully faithful single-complex result justifies representing it by a sheaf map, and that module linearity makes the map multiplication by a unit section. The cited constant-sheaf statement says precisely that this section is locally constant, and the action/trace base-change clauses give the claimed specializations. In Step 3 I checked the edge cases `d=0` and empty `S`, and verified directly that each geometric affine fibre has coordinate ring a nonzero polynomial domain, hence is connected. The zero section gives the identity translation, so the cited connected-locally-constant lemma forces the multiplier to be one on every fibre and the cited section/function identification then gives global equality. In Step 4 I checked that pulling back the universal square along the given section produces exactly `\tau_a`, `\operatorname{Ex}_{!,\tau_a}`, and `\kappa_a`, and that the two cited base-change formulas yield the displayed derived equality. The existing vector-integration site-comparison statement contains the exact ordinary-to-pro-etale trace identity used in the final sentence.

I ran the required LeanFinder, Loogle, grep, and LeanSearch searches twice with distinct phrasings. They returned only unrelated field-trace, measure-theoretic, affine-equivalence, or tensor base-change declarations; no Mathlib declaration states this finite-coefficient étale compact-support trace invariance. I made no Lean edits and ran no compiler or build tool.

What remains unfinished: nothing in this split; the new item is ready for the mandated dry run.
