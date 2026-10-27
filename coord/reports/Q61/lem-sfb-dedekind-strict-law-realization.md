## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dedekind-strict-law-realization.json`: the item, split into nine proof steps and no new nodes.
- `citations.json`: verbatim statement quotations for every cited dependency in every step.

## Attachments

No new Lean attachments. The existing field/DVR realization and rational homomorphism extension are cited as DAG nodes.

## WANTED

- Local copy of Conrad, *Reductive Group Schemes*, for Section 6.3 (the online PDF was read directly).
- Local copy of Bosch–Lütkebohmert–Raynaud, *Néron Models*, for the field/DVR realization and patching results already represented by existing nodes.

## What was checked and corrected

The imported item statement is retained exactly. It is stronger than the field/DVR node because the base is a Noetherian integral domain with DVR localizations at all nonzero primes, and it asks for a single global group scheme and open immersion. I found no sorry-free Lean declaration tagged with this item or stating the complete result. Existing DAG nodes already state the field/DVR realization, strict-law base change, finite-presentation spreading, closed-point patching, rational group-homomorphism extension, and the required scheme-theoretic locality facts, so I created no duplicate nodes.

The nine steps follow Conrad Section 6.3, pp. 224–225. Step 1 proves that the complement of the generic point is a finite set of closed points, using the DVR dimension and local-ring chain statements and the Noetherian finite-closed-points statement. Step 2 applies strict-law base change and the existing field realization. Step 3 spreads the finite-presentation source, group diagram, operations, and open chart along the directed system of principal localizations; the cited limit, spreading, property-descent, and finite-presentation nodes state each descent fact used. Step 4 preserves the fibrewise-dense chart after shrinking. It extends equality over the generic fibre from a dense witness to the entire original strictness domain by reduced schematic density and separated-target uniqueness, then spreads that equality by 01ZM(3).

Step 5 applies the existing DVR realization at each omitted closed point and uses the existing uniqueness of solutions over the generic field. Step 6 applies the closed-point finite-presentation patching equivalence, including its full faithfulness on arrows and detection of smoothness, separatedness, and open immersions, to glue the local group operations and chart. Step 7 compares the two morphisms into the group on the entire original strictness domain. They agree over the dense base open by step 4, and the domain is reduced and the pullback of that open is dense by smoothness. Reduced schematic density and separated-target uniqueness extend the equality over the special fibre. Step 8 uses Zariski scheme and morphism gluing; smoothness, separatedness, local finite presentation, quasi-compactness, and the open-immersion property are checked by the cited locality statements. Step 9 applies the existing rational group-homomorphism extension theorem to obtain the unique global group isomorphism between any two realizations.

I opened every cited node and copied its statement into `citations.json`; each step's hypotheses were checked against those statements. I also searched the whole DAG and blueprint for the strict Dedekind realization and for spreading/gluing duplicates. Mathlib searches for the item were run with LeanFinder, Loogle, LeanSearch, and grep; they returned only generic birational/rational-map or unrelated Dedekind declarations.

## Not duplicates

- `lem-sfb-dedekind-strict-law-realization` vs `lem-sfb-strict-birational-law-realization`: the existing node treats only a field or a single DVR; this item globalizes over a Dedekind domain and requires finite-point spreading and patching.
- `lem-sfb-dedekind-strict-law-realization` vs `lem-sfb-trait-birational-group-envelope`: the existing node is a local DVR envelope with a generic-fibre group; this item starts with a strict rational law over the entire Dedekind base and proves a global realization.
- `lem-sfb-dedekind-strict-law-realization` vs `lem-sfb-strict-law-base-change`: base change preserves strictness but does not construct a group realization.
- `lem-sfb-dedekind-strict-law-realization` vs `lem-sfb-closed-point-fp-patching`: patching is only an auxiliary descent construction for a finite presentation object, not the global strict-law realization.

## Review by Q61

I read the imported item node, the current six-functors chapter and unit records, Conrad Section 6.3 around Definition 6.3.10 through Proposition 6.3.13 and the Dedekind paragraph, and the cited Stacks limits and morphisms passages. I checked each proof step against the exact statement of every node listed in its `uses` field and recorded those statements verbatim in `citations.json`. In particular, I verified the DVR hypotheses at each nonzero prime, the finite complement argument, the qcqs and finite-presentation assumptions needed by the limit-spreading theorem, the generic-density hypotheses for shrinking, and the full-faithful arrow/equality clauses in closed-point patching. I corrected two initially overstrong approaches to rational compatibility: density in the generic fibre alone does not ensure density in the special fibre, and full faithfulness on morphisms alone is not a descent theorem for rational maps. The final proof keeps the original strictness domain and compares morphisms into the separated group there; reduced schematic density extends their equality from the dense base open. The smoothness and Noetherian hypotheses for these three cited statements are explicit. The final gluing step explicitly cites the scheme and morphism gluing statements and the target-open locality facts, and the uniqueness step cites only the existing rational group-homomorphism extension theorem.
