# Stage-1 delivery: lem-sfb-complete-local-smooth-power-series

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-complete-local-smooth-power-series.json: item, statement, eight-step split; not in Mathlib.
- dag/nodes/sec-six-functors-basics/lem-sfb-complete-local-cotangent-surjectivity.json: new statement-only node, Stacks 06GZ; not in Mathlib. No proof or proof dependencies are placed in it.
- citations.json: actual statement quotations for every step/node pair.

One new node; zero Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, formal smoothness, complete local rings, power series and cotangent surjectivity. The existing adic comparison map in FormallySmoothAdicPowerSeriesMap only gives a map with maximal-ideal and residue properties; it does not state this relative Artinian functor equivalence, power series isomorphism or tangent clause. The existing PowerSeriesAdicEvaluation source was read and is reused through its existing node, not reattached as this item. No Lean was written or compiled.

## WANTED

None. The needed Stacks sources are present locally.

## Errors and changes

The item's statement is correct and unchanged. The imported source has no proof; the split now writes the 06HL construction rather than treating the theorem as a black box. The square-zero test in the item is reconciled with the arbitrary Artinian-surjection convention in 06HL by the explicit nilpotent-kernel filtration. Formal smoothness here is the Artinian test for continuous local maps, not Mathlib's unrestricted algebraic FormallySmooth class.

The inherited blueprint.created chain is broken before an imported blueprint node: tools/blueprint_refs.py ancestor returns None. I retained the recorded null ancestor and full place/via chain, and gave the new node the same null ancestor and explicit place for the two 06GZ uses; I did not invent an ancestor. Read the chapter and unit records and the latest blueprint. This auxiliary commutative algebra calculation supports the existing nodal-deformation chain under the alteration input to det-thm-sf-ctf-stability-direct-images (3); it does not change the chapter or unit route. Generic power-series and Artinian quotient nodes from sk-thm-p1 are declared under split_report.tool_uses as required.

## Not duplicates

No existing node cites 06GZ. Searched the whole DAG for that tag, its label, cotangent surjectivity and complete local maps; searched the entire imported blueprint with blueprint_refs search for power series, cotangent, 06GZ and surjective cotangent. No blueprint or DAG node states this relative cotangent criterion. The existing lem-weil-pbc-complete-source-surjective-mod-ideal assumes surjectivity modulo the extended ideal; the new criterion starts with the strictly weaker relative cotangent hypothesis and needs the Nakayama argument to reach that assumption. It is not an exact match or a one-line specialization. The new node has no lifting or power-series-isomorphism conclusion and is not a clause of the item.

## Mathlib searches

Searches were run only with msearch.py. Their exact results are retained in search-results.jsonl (the extra item leanfinder response is summarized faithfully in the item) and the command's searches.jsonl. Read all hits, including the second cotangent phrasing, which found surjective_of_mk_map_comp_surjective. Read that declaration in Mathlib/RingTheory/AdicCompletion/Functoriality.lean at 447-459: its hypothesis is surjectivity of R to S/(I S), not of a relative cotangent map. The implication between these hypotheses is a substantive Nakayama argument, so the new 06GZ node remains unsplit. Quotient cotangent surjectivity and localizations found by the other searches concern different maps. Item searches found unrestricted algebraic smoothness lifting and no structure theorem; the prior 2026-10-22 item searches were retained intact and not represented as newly run searches. All services used in this run answered; none was falsely recorded unavailable or absent.

## Review by NN

I read formal-defos.tex, lemma-smooth-morphism-power-series (06HL), its entire proof, lemma-surjective-cotangent-space (06GZ), its proof and the Artinian precursor lemma-surjective; I also read example-tangent-space-map-prorepresentable-functor (06ST). For the sole new node, 06GZ (1) iff (3) says precisely the criterion stated, with coefficient base C and specified common residue k. The node introduces all rings, maps, completeness, locality, residue identifications and the relative cotangent quotients. Its Noetherianity and completion definitions are existing named nodes.

Step 1 uses exactly the maximal-ideal nilpotence and Noetherianity in lem-weil-pbc-artinian-local-noetherian-nilpotent. The finite kernel-power filtration is written out with 2j >= j+1; no uncited general formal smoothness equivalence is assumed. Eventual constancy of the quotients proves completeness of the Artinian target directly.

Step 2 uses the actual statements of power-series-noetherian, power-series-local-ring, power-series-quotient-variables and power-series-complete-over-complete-base. The local-ring node identifies the maximal ideal by constant coefficient, the quotient-variables node identifies its variable kernel, and their combination identifies it with m_B T+(X). Completeness uses precisely this combined ideal and B's assumed Noetherian completeness. None of these statements is taken merely from a definition or from its proof.

Step 3 applies power-series-adic-evaluation with the given coefficient map B to R-prime and maximal ideal of the Artinian target. Step 1 provides its completeness hypothesis; lifted variable values have zero residue because the quotient has the same residue field. I checked locality and maximal-ideal continuity explicitly, and use the evaluation node's stated uniqueness to show that reduction gives the prescribed map.

Step 4 cites the Noetherian definition only for finite ideal generators. The basis and finite-dimensionality are elementary linear algebra on a quotient killed by the maximal ideal. The combined-ideal-coefficients node at J=0,n=2 says exactly that a tail with zero constant/linear coefficients belongs to (X)^2. I wrote the square-zero multiplication, coefficient-field splitting, and coefficient test for independence, rather than citing a tangent definition as an identification theorem.

Step 5 uses noetherian-local-quotient-artinian-local with K between n^2 and n, and then n^j for j>=2: its containments and exponent hypotheses hold, so all lifting tests are on the allowed Artinian category. I checked the initial square-zero kernel K/n^2 and all successive n^j/n^(j+1) kernels. Every lift is a B-algebra map because the lifting problem includes the canonical B map to the target. Completeness is only the inverse-limit definition, cited by its exact statement; the ring map, locality and continuity follow coordinatewise as written.

Step 6 applies the new criterion twice with coefficient base C=B. Completeness and Noetherianity for A and B are hypotheses and for T are step 2. The relative cotangent map is the prescribed basis isomorphism. The section uses the existing evaluation statement with target A complete for m_A; its variable preimages lie in m_A by the residue identity. Its composite with f fixes all constants and variables, so uniqueness gives f s=1. On cotangents this gives the inverse of the already invertible map; hence the second use of 06GZ has its hypothesis. Surjectivity plus this left inverse proves an isomorphism with continuous inverse, with no assertion that an arbitrary split surjection must be injective.

Step 7 computes both directions of the duality on dual numbers, including the Leibniz rule, vanishing on m_A^2 and m_B A, and continuity. These are direct square-zero ring computations and use no uncited deformation-theoretic theorem. Step 8 is the specialization B=k and the actual meaning of prorepresentation; the singleton h_k and the dimension of a finite-dimensional dual give the last clause.

I checked delivery-errors B through E against the files: new node statement only, all its objects introduced, no invented search records, definitions and generic tool statements read, every citation quoted verbatim in citations.json, no dependency of the new criterion on the item or on its power-series conclusion. Each step is below 2000 characters and contains the explicit argument it claims. Edge cases: r=0 allows T=B and the empty basis; B=A yields the identity case; arbitrary residue characteristic never divides by an integer; no perfection or algebraic closure of k is assumed. The map k[[t]] to k[[t]], t maps to t^2, has zero cotangent map and is not surjective, so it does not satisfy the new criterion's hypothesis. The quotient k[[t]] to k[[t]]/(t^2) is surjective even though its cotangent map is an isomorphism; the criterion only concludes surjectivity, and the item obtains injectivity from its constructed section. Completeness is essential: k[t] localized at (t) to k[[t]] has the same cotangent space but the source is not complete. These checks distinguish the new lemma from a false cotangent-isomorphism criterion.

## Unfinished work

No part of this one-level split is left unfinished. The new criterion intentionally remains statement-only for its own later split. Validation and direct delivery follow with deliver.py, as authorized by the current brief.
