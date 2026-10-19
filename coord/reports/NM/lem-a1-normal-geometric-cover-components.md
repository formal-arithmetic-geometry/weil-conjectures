## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-normal-geometric-cover-components.json`: item, split into five proof steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-normal-etale-components-clopen.json`: statement-only child; no Mathlib match.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-geometric-cover-component-qc-proper.json`: statement-only child; no Mathlib match.
- `citations.json`: verbatim quotes for every cited node in every item step.
- `searches.jsonl`: actual `msearch.py` searches for the item and all three children.

## Attachments

None. A search of the read-only slopmaster2 source under `WeilConjectures/` found no declaration tagged `(blueprint: lem-a1-normal-geometric-cover-components)` and no finished declaration stating this item.

## WANTED

None.

## What was wrong or corrected

The imported item was unsplit and had no proof. I retained its exact hypotheses and conclusions, including the possibility that $Z$ is empty and that there may be infinitely many components. I corrected the split by making the source's substantive intermediate arguments explicit as two new statement-only children rather than treating the entire Lemma 7.4.10 proof as an elementary step. For the final image argument I reused the existing nodes `lem-weil-pbc-etale-morphism-open-map` and `lem-weil-pbc-finite-closed-map-finite-fibres`. The item uses the existing generic node `thm-pqf-finite-iff-proper-finite-fibres` as a tool after the geometric-cover child supplies properness and finite fibres; this is declared in `split_report.tool_uses` because it belongs to another unit. No SGA 4 source is used.

## Not duplicates

- `lem-a1-normal-etale-components-clopen` vs `lem-fin-etale-normal-components`: the new node treats an arbitrary etale source over a normal base and proves clopen components without assuming the source quasi-compact or Noetherian; the existing node assumes a Noetherian source and concludes normal integral components.
- `lem-a1-normal-etale-components-clopen` vs `lem-a1-normal-geometric-cover-components`: the new node is the clopen/irreducibility intermediate and has no valuation lifting, finiteness, or connected-base conclusion; the item proves the full geometric-cover component theorem.
- `lem-a1-normal-etale-components-clopen` vs `lem-a1-normal-locally-constant-finite-section`: the new node has no sheaf, local nonemptiness, or finite-cover section conclusion; the existing node constructs a finite etale cover carrying a section.
- `lem-a1-normal-etale-components-clopen` vs `lem-a1-normal-proetale-monodromy`: the new node is a topological component lemma with no coefficients or monodromy equivalence; the existing node classifies lisse adic modules.
- `lem-a1-normal-etale-components-clopen` vs `lem-a1-smooth-lisse-integral-lattice`: the new node has arbitrary locally Noetherian normal bases and no smooth finite-type or lattice data; the existing node constructs integral lattices.
- `lem-a1-geometric-cover-component-qc-proper` vs `lem-a1-normal-locally-constant-finite-section`: the new node is a scheme-theoretic component finiteness/properness lemma for a geometric covering and has no sheaf of sets; the existing node constructs one finite etale cover carrying a section of a locally constant sheaf.
- `lem-a1-geometric-cover-component-qc-proper` vs `lem-a1-normal-proetale-monodromy`: the new node has no coefficients or monodromy and only supplies the geometric-cover component route; the existing node classifies lisse adic modules and uses finite-cover descent.

## Could not finish

Nothing remains for this stage-1 split. The two children intentionally remain statement-only queue nodes, as required for one-level splitting.

## Review by NM

I read the item, the chapter `sec-purity-real-sheaves.json`, the unit `sk-p-real-rankin.json`, the ancestor blueprint node `lem-a1-affine-hc0`, the main-20261015 and master blueprint references, and the Bhatt–Scholze PDF at Definition 7.3.1 and the full proof of Lemma 7.4.10 on p. 71. I also read Stacks `properties.tex` Tag 0BQ3 (normal schemes are geometrically unibranch), Stacks `coherent.tex` Tag 02OG (proper with finite fibres is finite), and the existing DAG statements for the etale-open and finite-closed image facts. The read-only slopmaster2 source and upstream master source contain no finished declaration for this item.

Step 1 cites `lem-a1-normal-etale-components-clopen`; its statement explicitly supplies local topological Noetherianity, geometric unibranchness, and open-and-closed irreducible and connected components under exactly the normal and etale hypotheses. I checked that the item’s local-ring normality and local Noetherian assumptions match that statement. Step 2 cites `lem-a1-geometric-cover-component-qc-proper`; its statement explicitly supplies quasi-compactness, properness, and finite fibres for the induced map on each component under the connected, quasi-compact, normal base and the valuation lifting property. I checked the restriction of the lifting property: `Spec R` is connected, so a lift with generic point in a clopen component stays in that component, and uniqueness is inherited. Step 3 cites both that child and `thm-pqf-finite-iff-proper-finite-fibres`; the latter says exactly that a morphism over a locally Noetherian base is finite iff it is proper with finite fibres, so the induced etale map is finite etale. Step 4 cites the existing `lem-weil-pbc-etale-morphism-open-map` and `lem-weil-pbc-finite-closed-map-finite-fibres`; their statements give the open and closed image properties used, and connectedness of $X$ then gives surjectivity. Step 5 is elementary: maximal connected components are disjoint and cover the space, and clopen pieces glue to the disjoint-union scheme decomposition.

I tested the statement on `Spec k` with one finite separable component, an infinite disjoint union of copies of `Spec k`, the empty $Z$, and a proper open immersion into a normal connected scheme that fails the valuation lifting property. The finite-cover image is visibly all of `Spec k` in the nonempty cases. I checked every item step is under 2000 characters, every `uses` id exists, every use appears in `proof_deps`, and every citation quote is verbatim in `citations.json`. Mathlib searches used LeanFinder, Loogle, LeanSearch, and Mathlib source grep with second phrasings; all actual queries and outputs are recorded in `searches.jsonl`, with no match for the geometric-cover theorem or its three child statements. No statement was weakened, no target was changed, and there is no dependency cycle.
