# Stage-1 worker report: sk-lem-coefficient-heart

## Files written

- `dag/nodes/sec-six-functors-basics/sk-lem-coefficient-heart.json`: existing item retained and repaired; no new node.
The current unit record already realizes the statement and all five proof steps through this item. No unit file is delivered.
- `citations.json`: verbatim statement quotes for every proof-step citation.
- `searches.jsonl`: fresh Q41 searches from this continuation; historical searches in the existing item JSON are preserved as received.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag and the constructible-sheaf terminology; there is no sorry-free declaration carrying this item.

## WANTED

None. Bhatt–Scholze is present in `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`; the relevant passages are Definition 6.8.3, Corollary 6.8.5, Definition 6.8.6, Lemma 6.8.7, and Lemma 6.8.2.

## What was corrected

The interrupted delivery had no report, so the first dry run stopped before review. I restored the report and citations. I retained the imported split and all existing searches. I reread the current statements of all cited dependencies. The original final curve paragraph was 2548 characters and compressed several independent claims; I replaced it with three steps: (8) construction of the actual fibre-product scheme over generic neighborhoods and its surjective closed immersion, (9) descent of finite-free trivializations through the existing condensed-module equivalence for surjective closed immersions, and (10) the zero-dimensional finite complement and the open–closed exact sequence. This adds no node: every fact is already stated by an existing DAG node. I also added the existing quasi-separatedness node to step 1 and the existing reduced-induced-closed-subscheme node to step 10. The item statement, hypotheses, coefficient choices, and blueprint route are unchanged.

## Review by Q41

I read the item source `_section.md` and `sk-lem-coefficient-heart.proof.md` in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-coefficient-heart/`, the unit record, and the detailed source nodes `det-lem-coefficient-heart-common-stratification`, `det-lem-coefficient-heart-closure`, `det-lem-coefficient-heart-small`, and `det-lem-coefficient-heart-filtration`. I also read the Bhatt–Scholze PDF at §6.8: Lemma 6.8.2 identifies the coefficient sheaves, Corollary 6.8.5 gives kernels and cokernels of lisse field sheaves on topologically Noetherian schemes, and Lemma 6.8.7 gives constructible closure. The item’s standing hypotheses are finite type over a field, hence Noetherian by `lem-weil-pbc-finite-type-over-noetherian`; the open-subscheme and closed-subset Noetherian claims use the statements of `lem-weil-pbc-noetherian-open-subscheme-noetherian` and `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, and quasi-separatedness uses `lem-weil-pbc-locally-noetherian-quasi-separated`.

Step 1 uses exactly the Noetherian finite-type, coefficient-colimit, open-subscheme, closed-subset, and quasi-separatedness statements quoted in `citations.json`; I checked the field argument for `Spec k` and the hypotheses of each node. Step 2 uses the constructible definition, the closure lemma, and the finite-Tor-amplitude statement; I checked that `E` and `\Qlb` are fields, so finite presented scalar models are finite free. Step 3 uses the module extension-by-zero definition, cartesian coefficient identification, and the exact open–closed ringed-site lemma; I checked that the complement opens are quasi-compact and that the conclusion is exactness on module sheaves and descent to derived categories. Step 4 uses common-stratification and closure; their statements explicitly give exact restriction and lisse kernels/cokernels. Step 5 uses the common-stratification statement and closure statement for extensions; the local splitting argument is stated in the step and the cited closure node supplies the lisse conclusion. Step 6 uses the exact statement of `det-lem-coefficient-heart-small`, including fixed universes and the actual condensed coefficients, so no unsupported “descent data form a set” assertion is being substituted for that node. Step 7 uses the exact filtration statement, including non-strict inclusions and the closure-defined `a_!`; I checked its Noetherian and coefficient hypotheses.

For the curve specialization, step 8 uses finite irreducible components and unique scheme generic points, then forms `T=W_\eta\times_X S`; the immersion base-change and fibre-product-point statements justify that this is a surjective closed immersion, without assuming that set-theoretic containment gives a scheme factorization. Step 9 uses the existing cover-refinement node, the existing universal-homeomorphism statement for surjective closed immersions, the existing condensed coefficient-module equivalence, and cartesian coefficient pullback; these statements are exactly what the step takes, so the finite-free trivialization lifts to `W_\eta`. Step 10 uses the reduced induced closed subscheme statement, scheme sobriety for the `T_0` check, the zero-dimensional Noetherian-finite statement, and the exact open–closed sequence; it verifies the open immersion is quasi-compact and obtains the stated support on finitely many closed points. I checked the edge cases `X=\varnothing`, `F=0`, empty complement, reducible curves, and nonreduced schemes. The curve argument now makes the scheme structures and all non-elementary inputs explicit.

The existing item carries historical Mathlib searches; I preserved those records and ran fresh semantic searches with two phrasings, Loogle, grep, and LeanSearch during this continuation. LeanSearch returned a service-unavailable rate-limit response and is recorded as unavailable; Loogle and grep returned only ambient sheaf/condensed-category declarations, not this constructible-sheaf theorem. No Mathlib leaf or Lean attachment was found.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs.

## What remains

No unfinished split work remains. The initial dry run exited with the missing-report diagnostic; this report and citations repair it. The final dry run and delivery results are reported by the delivery tool.
