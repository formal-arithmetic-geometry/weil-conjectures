# Worker report: lem-sf-identification-exchange-comparison

Files written:

- `dag/nodes/sec-six-functors/lem-sf-identification-exchange-comparison.json` — statement node, split; no new Mathlib leaf.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.
- `report.md` — this report.

Attachments: none. I searched the slopmaster2 source for the item id, blueprint tag, and the naturality-comparison terminology; no sorry-free declaration states this item exactly. The nearby tensor–Hom, Verdier-exchange, and global-duality declarations do not state the displayed comparison as a finished declaration.

WANTED: none.

No statement correction was needed. The imported node had an empty proof and stale Mathlib-search records (including an invalid historical grep directory); I replaced those records with searches actually run by `msearch.py` on 2026-10-18. No new supporting node was necessary. The proof deliberately does not cite the item itself: it expands the naturality calculation that the parent global-duality proof had referred to by this item's id.

## Review by Q24

I read the item, its chapter and unit records, the current main-20261015 source `sk-thm-sf-identification.proof.md` (the paragraph beginning “Step 3: naturality of tensor–Hom in N, evaluation comparison, and identification with global duality”), and the statements of every cited node. The item hypotheses are retained: the fixed six-functor datum, all four coefficient realizations, the smooth separated geometrically connected finite-type X, the structure map to the point, and the constructible finite-Tor hypotheses on K. The coefficient-transport statement supplies that the identity counit ν and its exceptional pullback c are isomorphisms with c = Ra^!(ν) at the actual completed, rationalized, or common-stage operation.

Step 1 uses the statement of `sk-thm-sf-tensor-hom`, which explicitly gives a canonical exchange natural in M and N, and the coefficient-transport statement, which identifies c with Ra^!(ν) at every stage. I checked that the source and target of the naturality square are respectively the exchanges at ω_s and Λ_s, giving exactly `b_1 ∘ Ra_*RHom_X(K,c) = RHom_s(C,ν) ∘ b_ω`. Step 2 is the formal two-sided cancellation in the definition of the Verdier exchange named in the item; no external theorem is hidden in that step.

Step 3 uses `lem-sf-identification-fibre-adjunction` for the evaluation-preserving point comparison α_C^1 and `lem-sf-point-fibre-derived-tensor` for the natural tensor and unit comparisons. I checked that applying the target map ν to the evaluation square produces `α_C = α_C^1 ∘ Fib_s RHom_s(C,ν)`, with the same interpretation before integral completion and after the prescribed field realizations. This is the only cross-unit generic tool use, and it is recorded in `split_report.tool_uses`.

Step 4 uses the statement of `sk-thm-sf-global-duality` for the canonical point-category duality map. Unfolding the construction described in the item gives `G = Fib_s(η_K) ∘ α_C^{-1}`; substituting Steps 2 and 3 cancels the two inverse internal-Hom factors and yields `G = Fib_s(b_1^{-1}) ∘ (α_C^1)^{-1}`. I checked all compositions have the displayed source and target and that no properness hypothesis is introduced beyond the global-duality node's alternatives.

I checked small formal edge cases (K=0, identity ν, and either fibre comparison an identity): every displayed equation reduces to an identity or the corresponding exchange map. The four required Mathlib search kinds were run for the item; they returned only generic monoidal curry/naturality declarations and no six-functor statement. The server `check_dag` and `review_split` checks both passed, with no new nodes and the point-fibre tool use recorded.

What could not be finished: nothing.
