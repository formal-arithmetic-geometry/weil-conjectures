# Stage-1 report: lem-trf-valuation-ring-ideal-correspondence

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-ring-ideal-correspondence.json` — statement, split into four direct proof steps; no new nodes; Mathlib verdict: no exact match.

## Attachments

None. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration tagged `(blueprint: lem-trf-valuation-ring-ideal-correspondence)` and no declaration stating this correspondence.

## WANTED:

None. The Stacks source is present locally. Tag 00IH states the result but omits its proof; the report records the direct value-set proof supplied here.

## What was wrong or incomplete

The imported node had an empty proof and `status: unsplit`; its `created` metadata came from an earlier worker/item, but the mathematical statement and imported searches were retained. The blueprint has no node stating this correspondence directly; the item is a dependency of the valuation prime/convex-subgroup node. I filled the missing proof and blueprint `same_as`/`from.place` metadata. No duplicate DAG node was found for Tag 00IH or for the value-group ideal correspondence.

## What could not be finished

Nothing. The theorem's published proof is omitted in `literature/stacks-project/algebra.tex`, so the proof is marked agent-written and derives every claim directly from the displayed valuation-ring and value-group definitions.

## Review by Q110

I read the item node, the valuation-ring definition node `def-trf-valuation-ring`, and the Stacks source around `algebra.tex` lines 12077–12093 (Tag 00IH) and the preceding Tag 00IE value-group conventions. I also checked the ancestor blueprint node `lem-trf-local-term-locality` and its Temkin §2.1 reference. The item hypotheses are exactly a field K, a valuation ring A in K, and the quotient ordered group Γ; no coefficient or geometric hypotheses are present.

Step 1 defines the value-set map from an A-ideal and checks representative-independence, existence of representatives for nonnegative classes, and upward closure using the quotient order. Step 2 defines the inverse map from an upward-closed value-group ideal and checks multiplication and addition; for addition I explicitly used the valuation-ring alternative to arrange `[a] ≤ [b]`, giving `(a+b)/a = 1+b/a ∈ A`, with the zero-sum case handled separately. Step 3 checks both composites and inclusion preservation. Step 4 checks prime ideals in both directions, including the domain argument for zero products and the equivalence between `0 ∉ I` and properness of the associated ring ideal. These are all direct calculations from the statement's definitions, so no external node is cited and `citations.json` is the empty list.

I ran all four required Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch); their hits concern valuation ideals or prime-spectrum correspondences but none states the value-group ideal bijection. The server `check_dag` preflight passed with no introduced finding.
