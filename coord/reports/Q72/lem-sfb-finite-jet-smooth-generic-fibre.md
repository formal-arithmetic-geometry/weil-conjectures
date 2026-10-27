# Q72: lem-sfb-finite-jet-smooth-generic-fibre

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-jet-smooth-generic-fibre.json`: statement node, now split in nine steps; not in Mathlib. The only statement-text change is placing the already-listed power-series definition citation at `R=k[[t]]`.
- `citations.json`: 19 citation records, each containing the verbatim statement of the node used by that step.
- `searches.jsonl`: five searches made with the authorized msearch command; all services answered. The original item's earlier search evidence is preserved in its JSON and the five new queries/results are appended.
- This report. `write_split.py` is a sandbox-only preparation script, not a delivered node or project tool.

New nodes: **0**. New Mathlib leaves: **0**. All needed notions and auxiliary statements already exist.

## Attachments

None. I searched the live `lean/WeilConjectures/` both for the blueprint item tag and for Fitting, Cohen–Macaulay and finite-jet/generic-fibre terminology. No project declaration states this criterion. The smoothGenericDirectImage hits concern constructible direct images, and the Cohen–Macaulay-locus declarations only supply auxiliary geometry. They do not prove the item's conclusion under its hypotheses.

## WANTED

None: the Stacks source and its cited inputs are available under `literature/stacks-project/`.

## Changes and issues found

The imported item had no proof. Its statement agrees with examples-defos Tag **0E7T**, `lemma-criterion-smoothing`. The source uses `k[t]/(t^n)` while the item uses `k[[t]]/(t^n)`; truncating coefficients identifies them. The source assumes proper and flat; the item's finite-presentation assumption adds no effective restriction over this noetherian base, but I preserved it exactly.

The short source proof leaves two properness uses implicit: the open Cohen–Macaulay locus containing the special fibre is all of Y, and the clopen dimension pieces with wrong dimensions are empty. Steps 2–4 now explain these uses through the fact that a closed image in Spec k[[t]] missing its closed point is empty. Steps 7–8 expand the source's stalk-to-neighbourhood calculation and its last properness inference.

I did not apply `lem-trf-dth-fitting-smooth-locus` directly: its statement assumes equidimensional **geometric** fibres, whereas the existing dimension-partition statement gives ordinary local fibre dimensions. Step 5 instead cites the existing Fitting-generator theorem and pointwise smoothness/differential criterion, which together give exactly the needed ordinary-fibre formulation. This is the argument of source 0C3K, using its existing smaller DAG interfaces, and does not replace a unit step or change the route.

## Not duplicates

No new node is proposed. I searched the whole DAG by the source labels and tags 045U, 02NM, 0C3K and 0C3I, and by Cohen–Macaulay, Fitting, smoothness and differential base-change concepts. Existing nodes give all the tools. Whole-blueprint searches for `Fitting`, `Cohen` and `smoothing` found no equivalent imported statement; the smoothing hit `lem-fin-generic-radicial-smoothing` is a radicial alteration statement over a finite-type base, not this infinitesimal criterion. The item's inherited blueprint ancestor is null (`blueprint_refs.py ancestor`); its precise inherited `from.place` and via chain are preserved and `same_as` remains empty.

## Unfinished work

None in the authorized stage-1 split. The existing auxiliary nodes retain their own stage states; no Lean was written or compiled and no project or launcher file was changed.

## Review by Q72

I read the item against `examples-defos.tex` Tag 0E7T, including its proof, and read its chapter and unit records, the three-level contract in SETUP, and delivery-errors B–E. This is the finite-jet prerequisite already named in the inherited blueprint route to the direct-image finiteness theorem. No chapter or unit file is changed. There are no new nodes whose statements or sources need a separate review.

For **Step 1**, I opened `lem-weil-pbc-power-series-field-cohen-regular-complete` and Algebra Tag 032C (`remark-Noetherian-complete-local-ring-universally-catenary`). Its field/one-variable case supplies localness, domain, residue field k, maximal ideal (t), and dimension one. The argument excluding a third prime is a chain-of-primes argument, not an unquoted DVR theorem. The power-series definition supplies the coefficient truncation and Laurent-series identification. I checked that t is nonzero, so the two primes really are distinct.

For **Step 2**, I read the entire proper-morphism definition. Its universally closed clause, at the identity base change, says precisely that f is a closed map. Applying that to a closed set missing the whole special fibre yields the asserted empty image in this two-point base. The proof never assumes the restriction of a proper morphism to an open source is proper. This elementary observation is then reused, not promoted to a duplicate node.

For **Step 3**, `lem-sbc-fibre-cohen-macaulay-locus-open` explicitly gives openness for a flat locally finitely presented morphism with the depth-equals-dimension condition used here. I compared its statement with More on Morphisms Tag 045U, `lemma-flat-finite-presentation-CM-open` (1),(2). Both morphism hypotheses are assumptions on f, and the given special-fibre condition places every special-fibre point in that open. The closed complement is handled by Step 2. This proves the condition on all fibres, not merely on their generic points.

For **Step 4**, I opened the dimension-decomposition node and verified that its source open W can be Y after Step 3, with base open S. Its statement provides pairwise disjoint opens covering Y and gives the local topological dimension of the original fibre at each point, exactly what the step uses. Disjointness and coverage make each open also closed. I read Morphisms Tag 02NM, `lemma-flat-finite-presentation-CM-fibres-relative-dimension`, and Varieties Tag 0A21 (3),(5). The equidimensional-open local-dimension node assumes locally finite type over a field; the cited permanence node's clause (3) supplies local finite presentation after base change to k, and the definition immediately implies local finite type. Thus all special-fibre points have local dimension d, and every wrong-dimensional closed piece is disjoint from the special fibre and empty. I kept local topological dimension distinct from dimension of the local ring at a nonclosed point.

For **Step 5**, I read the Kähler-differential definition, the relative-differential-sheaf affine definition, the full statement of the Fitting-generator node, and the full pointwise differential-criterion node. The generator node's clause (2) gives a **stalk** generator condition, and the smoothness node uses precisely that condition with the ordinary fibre dimension from Step 4 and local flatness from the flat-morphism definition. The local finite-presentation hypothesis is present. I read Divisors Tags 0C3K, 0C3F and 05P8 and Morphisms Tag 01V9 (1),(3), and checked finite generation directly: the derivation relations express d of every algebra element using the finitely many dxi. Thus no missing finite-type-differentials theorem is hidden in this step.

For **Step 6**, I read the complete statements of the differential base-change and Fitting independence/base-change nodes and the sources Algebra Tag 00RV, More on Algebra Tag 07ZA (3), Morphisms Tag 01V0 and Divisors Tag 0C3I. These assertions allow arbitrary base change, so no flatness of R/(t^n) is being assumed. The tensor is A_n tensor_A Omega_{A/R}; the base of its differentials is R_n, not R. The Fitting formula is the image ideal (I+t^n)/(t^n), not a claimed isomorphism from the tensor pullback of an ideal into the structure sheaf. Applying the two displayed formulas on affine charts and using the cited localization compatibility is an elementary combination of existing statements, so I did not create a scheme-level duplicate node. The hypothesis gives stalk membership, and no global lifting of sections is asserted.

For **Step 7**, I checked the explicit equality t^(n-1)=b+t^n a, hence (1-ta)t^(n-1)=b, in the local ring at a special-fibre point. The image of t is in its maximal ideal, making 1-ta a unit. The argument does not cancel t and does not require a reduced special fibre.

For **Step 8**, equality of germs is used only after shrinking the representative's domain; the ideal is an actual subsheaf, so this follows from the definition of a stalk. Prime ideals containing t^(n-1) contain t for n>1. For n=1 the unit ideal has empty vanishing set, and that case is handled separately. The union of the neighbourhoods contains the entire special fibre, so its closed complement is empty by Step 2. In particular, the final properness inference is about a closed complement, not the nonclosed generic part of Z.

For **Step 9**, I opened the smooth-relative-dimension permanence, open-immersion-etale and etale-source-smoothness nodes. The first requires smoothness of fixed relative dimension, so I explicitly supplied dimension d from Step 4 on every smooth neighbourhood before using its base-change clause. The resulting generic-fibre opens form a jointly surjective family; their inclusions are etale by the second node, and the third node's statement then gives smoothness of the whole generic fibre, with no unstated quasi-compactness condition. I read Morphisms Tags 01VB and 02GP and Descent Tag 036U, `lemma-smooth-smooth-local-source`. All these off-unit geometry statements are declared as generic tools in `split_report.tool_uses` with their individual purposes.

I checked **B1–B10**: no new nodes, no hidden proof sketches in statement-only children, all notation has existing definitions, the source tags/labels are explicit, no claim of a Mathlib match or attachment is made, and the exact real search queries/results are recorded. I checked **C1–C8** by opening every cited node's statement; the verbatim citation records cover all 19 uses, and every non-elementary inference is supported by a cited statement rather than a source tag or the proof of another node. The elementary steps are the closed-map argument, the combination of the two affine base-change formulas, and the written local-ring/stalk arguments. All other steps are marked non-elementary. The generic-tool declarations explain the cross-unit citations.

I checked **D1–D5**: no clause is moved into a new node, there is no self-reference or new child dependency, and the source's abbreviated arguments are carried by the steps themselves. Every step is shorter than 2000 characters. I checked **E1–E7** on n=1, d=0, an empty special fibre, an empty Y, arbitrary characteristic and an imperfect k. If X is empty, properness forces Y empty. For n=1 the bound makes the Fitting ideal the unit ideal near the special fibre. No perfectness, geometric equidimensionality or reducedness was added; base change of differentials is arbitrary, and the dimensions in Step 4 are not local-ring dimensions at generic points. I found no statement dispute or source error to repair.
