# Q41 stage-1 report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-fppf-etale-finite-free-refinement.json` — item, statement split, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-fppf-local-qf-refinement.json` — new statement-only Tag 0572 input, no Mathlib match.
- `citations.json` — verbatim statement excerpts for every item-step citation.

Attachments: none. No sorry-free project declaration states the item. No `WANTED:` items.

## Not duplicates

- `lem-trf-fppf-local-qf-refinement` vs `lem-trf-fppf-local-finite-free-refinement`: the existing node asserts a two-level Zariski/finite-locally-free refinement, while the new node is the strictly earlier Tag 0572 refinement by flat locally finitely presented locally quasi-finite maps and maps to original cover members.
- `lem-trf-fppf-local-qf-refinement` vs `lem-weil-pbc-etale-local-finite-multiple-points`: the existing node is an etale-local finite-open theorem for isolated fibre points; the new node constructs a covering refinement of an arbitrary fppf family and has no etale or finite conclusion.

The item is Tag 0DET itself; the existing `lem-trf-fppf-local-finite-free-refinement` uses it as an input and therefore is not a duplicate of the item's statement.

## What I checked

I read the item, the fixed Trace Formula chapter and `sk-i-curve-zero` unit, and the complete Stacks proof of Tag 0DET in `literature/stacks-project/more-morphisms.tex`. I also read Tag 0572 (the new child), Tag 045U (fibrewise Cohen–Macaulay density), Tag 0570 (the flat locally quasi-finite slice), Tag 02LK (the existing etale-local finite-multiple-points node's source), and the cited permanence facts Tags 01U9, 01TS, 01WL, 01UA and 053N. The target statement retains every hypothesis and conclusion of 0DET, including arbitrary schemes, small families, and empty cases.

The new child records the Tag 0572 construction. For each point of the base I use joint surjectivity to select an original cover member, choose a closed Cohen–Macaulay point in its finite-type fibre using the existing density node and the closed-point criterion, and apply the existing Tag 0570 slice statement. The resulting family is jointly surjective because each selected slice contains the point used to select it; the factorization through the original member and smallness are explicit.

For the item, Step 1 handles empty base and empty family and fixes the universe bound. Step 2 cites the new child for flatness, local finite presentation, local quasi-finiteness, and factorization, then cites the isolated-fibre consequence with the correct point hypothesis. Step 3 applies the existing multiple-point etale theorem to a singleton list, and uses the fibre-product relation to retain the factorization map. Step 4 checks every inherited hypothesis: finite and flat base change, locally finite presentation under base change and open restriction, the definition of finite locally free, and openness of flat locally finitely presented maps. Shrinking to the open image makes each finite locally free map surjective while preserving the etale neighbourhood and factorization. Step 5 verifies joint surjectivity, small indexing, and the original refinement maps.

I searched the full DAG and blueprint for Tag 0572, its labels, and the phrases “locally quasi-finite fppf refinement”; no existing node states it. I ran LeanFinder, Loogle, grep, and LeanSearch for both the item and the new child; the searches found only generic covering, etale, flatness, and locally quasi-finite declarations, with no theorem matching either statement. All search invocations are recorded in `searches.jsonl` and represented in the node's `mathlib_searches`.

No source or statement error was found. Small cases checked are the empty base, empty family (which forces an empty base), the identity cover, and a singleton fppf cover; the construction is vacuous or reduces to the stated pointwise argument in each case. No SGA source is cited and no long proof step hides an additional independent lemma.

## Review by Q41

I re-read every item proof step against the exact cited node statements. Step 2 takes precisely the locally quasi-finite, flat, locally finitely presented, jointly surjective family and its factorization from the new child, then uses the existing isolated-fibre theorem only after verifying local quasi-finiteness at the selected point. Step 3 uses the existing multiple-point theorem at `n=1`, so its finite open and unique point clauses apply directly; the fibre-product node supplies the displayed composite equality. Step 4 uses only permanence statements that explicitly cover base change or open restriction, and the finite-locally-free definition exactly matches the three properties established. The flat-lfp-open leaf explicitly supplies the open image used for the surjectivity shrink. Step 5 uses the definitions of surjective, etale, and the universe size convention for the final family. I checked the empty cases and the singleton/identity examples, and verified that no cited statement is a definition standing in for a theorem or a weaker special case. The only new node is strictly below the item and differs from the existing two-level refinement node; its proof dependencies and Mathlib searches are complete.
