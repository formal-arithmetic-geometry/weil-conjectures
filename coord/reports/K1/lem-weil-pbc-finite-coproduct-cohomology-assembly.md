# Delivery report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-finite-coproduct-cohomology-assembly.json`: item, statement, Mathlib verdict no match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-etale-sheaf-clopen-product.json`: new statement node, Mathlib verdict no match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-derived-finite-product.json`: new statement node, Mathlib verdict no match.
- `citations.json`: verbatim quotes for every node cited by every proof step.

2. Attachments: none. No exact sorry-free declaration carrying the item was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator`.

3. WANTED: none. The Stacks source file used for the route is available at `/home/ubuntu/c1-stacks-review/etale-cohomology.tex`; the repository citation table identifies Tag 0A5B as `etale-cohomology-lemma-constant-smooth-statements`.

4. What was wrong or incomplete: the imported item had an empty proof, so the finite-product assembly was not split into its categorical and derived-functor ingredients. I added two strictly smaller statement-only nodes and made the item proof use them. The item statement and its existing statement dependencies were retained. No duplicate blueprint node was found by `tools/blueprint_refs.py search` or DAG keyword searches. The source's phrase “the etale site is a finite product” was made precise as an equivalence of abelian-sheaf categories with componentwise global sections; the derived-functor consequence was stated separately.

5. What I could not finish: no Lean code is written at stage 1. The repository-wide `check_dag.py` invocation reports pre-existing reachability and route diagnostics unrelated to these files; the delivery preflight is the authoritative sandbox check.

## Review by K1

I read the item, its blueprint ancestor `lem-weil-pbc-zero-dimensional-cohomology`, the unit `sk-prop-cd`, and the Stacks proof of Lemma 0A5B in `etale-cohomology.tex` (the paragraph beginning “Since X is smooth…” at the finite disjoint-union reduction). I also read the statements of `lem-weil-pbc-scheme-coproduct-family`, `def-weil-pbc-inverse-image`, and `def-weil-pbc-etale-cohomology` before citing them. Step 1 uses only the scheme-coproduct statement, whose text explicitly gives open immersions, pairwise disjoint images, coverage, and the clopen consequence. Step 2 uses the new clopen-product node, whose statement explicitly gives the sheaf-category product, recovery by inverse images, componentwise morphisms, and product global sections; the inverse-image definition is cited for the notation. Step 3 uses the etale-cohomology definition for K-injective derived global sections, the clopen-product node for the product functor, and the new derived-finite-product node for the natural product formula for every degree. Each citation is recorded verbatim in `citations.json`.

For both new nodes I searched the whole DAG and blueprint before creating them, then ran LeanSearch, LeanFinder, and Mathlib-source grep searches. No exact Mathlib result exists. The new statements were tested on the empty index set (empty product and zero sheaf) and the singleton index set (the identity decomposition); both reduce to the corresponding component statement. I checked that all hypotheses are present: finite indexing, clopen coprojections, abelian etale sheaves, and enough injectives for the derived-functor node. The item’s blueprint `from.place` was already the exact finite-product paragraph and remains filled; `split_report.blueprint` records how all three steps realize that paragraph.
