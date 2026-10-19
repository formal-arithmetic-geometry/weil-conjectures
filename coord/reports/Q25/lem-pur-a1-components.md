# Stage-1 report: lem-pur-a1-components

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-a1-components.json`: statement, split into ten proof steps; Mathlib does not state the complete geometric assertion as a one-line specialization. No new nodes and no new Mathlib leaves.
- `citations.json`: fourteen entries, one for every step/node pair, quoting each cited statement verbatim and in full so its hypotheses remain visible.
- `report.md`: this report. `searches.jsonl` was written by the authorized search command. `write_split.py` is a sandbox-only preparation script, not a delivery file.

## Attachments

None for the item. Searches for the exact blueprint tag, the ID, affine-line component terminology and the unit's Lean names found no project theorem stating all three clauses. The nearby `WeilConjectures/EtaleCohomology/Purity/Smooth/AffineLine.lean` states sheaf-map uniqueness, not the component assertions; it also contains sorry declarations, which have not been treated as finished proofs. The affine-space extensions provide sections and affine-space constructions, not this item's full statement.

The existing dependencies `sbc-lem-affine-space-smooth` and `sbc-lem-smooth-criterion` already have closed Lean audit records. I read the affine-space smoothness instance in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`; it applies over every scheme, in particular to the singleton coordinate type. I did not alter those nodes or claim a new attachment for them.

## WANTED

None. The repository's untracked literature files are absent on this machine, but the matching blueprint document and Stacks sources are available read-only under `/home/ubuntu/work-bp/sheaf/literature/`. Those are the physical files read. JSON citations retain their canonical `literature/...` document paths.

## Statement corrected

STATEMENT-DISPUTED: the imported formula uses ordinary `Spec(O_B[t])` when `O_B[t]` is a sheaf of algebras on a potentially nonaffine base, not a commutative ring. For example, take the allowed base B = P^1_k. There is no ordinary ring spectrum whose input is this sheaf. Interpreting the input as global sections instead gives Spec(k[t]), dimension one, whereas the intended affine line over P^1 has dimension two. The correction is the relative spectrum `underline{Spec}_B(O_B[t])`, exactly the construction in the already reviewed `def-sbc-affine-space` and Stacks Tag 01M0, label `definition-affine-n-space`.

All three component/intersection conclusions and every original hypothesis are retained. I added definition citations for separatedness, finite type, closed immersion and connectedness, and spelled out that a connected component is a maximal nonempty connected subset. The two existing citers, `prop-pur-a1-invariance` and `lem-pur-lisse-uniqueness`, continue to use precisely the same component geometry; neither relies on an ordinary spectrum of global sections.

## What was wrong and what changed

The imported proof compressed smooth-to-flat, openness, fibre identification, and the Noetherian component argument into a single step with too few dependencies. In particular its `def-weil-scheme-morphism-properties` citation is a catalogue, not a theorem that finite type implies Noetherian or that connected components are clopen. I removed that citation and the unnecessary Noetherian detour.

The replacement follows the same unit step (i): open line and punctured-line projections with connected fibres, then connected components, then the unit section. Smoothness implies flatness and local finite presentation by the existing `sbc-lem-smooth-criterion`, and openness follows from the existing Mathlib leaf `lem-weil-pbc-flat-lfp-open`. Openness of the punctured-line projection follows simply by restricting to an open subset; no composition or flatness-stability fact is silently invoked. Fibres of the line are computed from the pullback definition of affine space, with associativity proved directly by its universal property. Leading coefficients prove the polynomial ring is a domain; the dense zero prime gives connectedness of both fibres, with the punctured fibre treated as a nonempty open subspace. Finally the existing connected-fibre quotient node is applied after restricting to a base component. This restriction avoids any unproved assertion that a component is open or closed in the original base.

## Mathlib and duplicate searches

The seven search records in the item are exactly the queries run through `/home/ubuntu/weil-launcher-nt/msearch.py`; their outputs were read. LeanSearch returned Internal Server Error and is recorded as unavailable. LeanFinder and Loogle returned generic component/quotient theorems and affine-coordinate constructions; source grep returned affine-space irreducibility instances and the topology lemmas. A second semantic phrasing found the useful generic connected-fibre result, which is already represented by `lem-weil-pbc-connected-fibres-quotient-preimage-connected`. I read that node's full statement and Mathlib `Topology/Connected/Clopen.lean:404` rather than making a duplicate.

Whole-DAG searches included connected fibres, quotient/open maps, polynomial domains, affine-space base change, and affine-line components. Blueprint searches included `affine space`, `affine line`, `connected components of the affine`, `geometrically irreducible`, and `connected fibres quotient`; the ancestor command confirms this item is itself its blueprint ancestor. No other blueprint node states all three clauses, so `blueprint.same_as` is empty. The generic connected-product-components node is a different theorem and is not needed. No new node was created.

## Not duplicates

No new nodes. Existing results are cited directly, including the already available Mathlib leaf for quotient maps with connected fibres.

## Unfinished work

None for this split. There are no new statement-only obligations. No Lean files were written, no compiler or Lake/build tool was run, no live files were changed, and no push is requested. The sandbox is reserved for the fresh second reader.

## Review by Q25

I read the item's blueprint proof, the chapter record and unit `sk-prop-a1-inv` before finalizing the split. The item supplies the component geometry of unit step (i); it is not the unit's key statement, so no unit realization file is changed. The route is still the unit's connected-fibre argument. Its geometric inputs are tools already represented by closed nodes or Mathlib leaves, so no off-route unclosed tool is introduced.

For Steps 1-2 I checked Stacks morphisms.tex, Tags 01VE (`lemma-smooth-locally-finite-presentation`), 01VF (`lemma-smooth-flat`), and 01UA (`lemma-fppf-open`). I opened all three cited node statements: affine-space smoothness gives the projection over an arbitrary base; the smooth criterion explicitly supplies flatness and local finite presentation; the flat-lfp node explicitly supplies openness. Both hypotheses of the openness theorem are thus established. The punctured line is an open subset because the zero section is closed, and an open subset of an open subset is open. The unit section proves surjectivity point by point. I corrected the original argument by using this topological restriction instead of silently invoking scheme-theoretic composition/stability results.

For Step 3 I read constructions.tex Tag 01M0 and its following base-change formula, and schemes.tex Tags 01K0/01K1. The cited affine-space node really gives the fibre-product construction and the polynomial spectrum on affine bases. The fibre node really gives both the residue-field pullback and the homeomorphism onto the topological fibre. The fibre-product node really gives the universal property and uniqueness of its comparison maps. The compatible-pair argument is included explicitly; no affine base B is assumed. It works at arbitrary nonclosed points as well.

For Steps 4-5 I read algebra.tex's definition of the spectrum, its Zariski closed subsets V(I), and the polynomial-domain discussion in Tag 030A; only the elementary leading-coefficient calculation is used, not the stronger normality assertion of 030A. I opened the field, polynomial-ring, affine-spectrum and connectedness nodes. The polynomial node explicitly gives the convolution product and leading coefficient, and the field node gives nonzero products. The spectrum node gives the prime-ideal space and Zariski topology. I wrote why (0) is prime, why its closure is the entire spectrum, and why this prohibits a separation. The punctured topological fibre is an open subspace and contains the actual unit-section point 1(y); no unstated assertion that localization preserves a domain is used.

For Steps 6-7 I read topology.tex Tags 0377/0378 and the full existing node `lem-weil-pbc-connected-fibres-quotient-preimage-connected`, then checked its exact Mathlib declaration at Clopen.lean:404. That node requires a continuous map, every fibre connected and nonempty, the quotient topology, and a closed connected subset of the target. Step 6 proves the restricted map is continuous, open, surjective, and quotient, and carries the established fibre connectedness. In Step 7 the closed subset is the WHOLE restricted target D, not a subset falsely assumed closed in B. All hypotheses of the cited node hold, and its conclusion is exactly the connectedness needed. This is the only non-elementary topology input.

For Steps 8-9 I read topology.tex Tags 004S, 004T and 0376. The only cited definition is nonempty connectedness, and the text proves the image and union assertions directly: separation pulls back to a separation, and a union of connected subsets with a common point cannot have points on both sides of a separation. I verified that surjectivity gives D contained in the image in Step 8, which is necessary for maximality. Step 9 constructs a component through each base point by taking all connected subsets through that point, then proves the two intersecting maximal connected sets agree. No finiteness or clopen-components theorem is being smuggled into these steps.

Step 10 uses the sections already specified in the statement: for each nonempty component D, a chosen y in D gives 1(y) in both corresponding components. This simultaneously gives both intersection assertions for the affine line and the assertion for the punctured line; no clause is omitted.

I checked the B-E delivery checklist with the node and these sources open. There are no new nodes to fail B's self-contained/statement-only/duplicate rules. Every use has its actual supplying statement, and `citations.json` quotes all fourteen such step/node pairs; the proof uses statements, not hidden constructions in other nodes' proofs. Each non-elementary result is cited. The elementary steps carry their arguments rather than hiding them in new nodes, so neither an item clause nor the whole item has been relabelled as a new lemma. A read-only graph traversal found no missing, merged or cyclic dependency introduced by the split.

Small-case checks: B = Spec(k) gives the connected affine and punctured lines containing t=1; a disjoint union of two points gives exactly two components in each, both hit by the section; a connected reducible or nonreduced finite-type B still has polynomial residue-field fibres, and the quotient argument needs no reducedness or irreducibility of B. B = P^1_k checks the corrected relative-spectrum formula and the nonaffine fibre computation. Positive characteristic does not affect the leading-coefficient argument or the fact that 1 differs from 0 in residue fields. The empty-base case would be vacuous although the item's original nonemptiness assumption is retained. No new statement was introduced that needs a separate edge-case audit.

## Second reading by Q25

- Step 1 checked against Stacks Tags 01VE, 01VF, 01UA and the three cited node statements; smoothness supplies flatness and local finite presentation, and openness applies: PASS.
- Step 2 checked against the closed-immersion definition and the relative topology of an open complement; the restriction, continuity, surjectivity, and unit-section claims are elementary and correct: PASS.
- Step 3 checked against Stacks Tags 01M0, 01K0, 01K1 and the affine-space, fibre, and fibre-product node statements; the residue-field fibre identification is valid over arbitrary points: PASS.
- Step 4 checked against the spectrum, polynomial-ring, field, and connectedness definitions and the elementary leading-coefficient calculation; the dense zero prime proves connectedness: PASS.
- Step 5 checked against Step 4 and the open-subspace topology; the generic point lies in the punctured fibre and every nonempty relative open contains it: PASS.
- Step 6 checked against Stacks Tag 0378 and the restriction topology; the restricted map is continuous, open, surjective, and quotient without assuming components are clopen in the base: PASS.
- Step 7 checked against Stacks Tag 0377 and the full statement of `lem-weil-pbc-connected-fibres-quotient-preimage-connected`; applying it to the whole connected target component supplies connectedness: PASS.
- Step 8 checked against Stacks Tags 0376 and 004S and the connectedness definition; the image argument and maximality argument establish that each preimage is a component: PASS.
- Step 9 checked against Stacks Tag 004T and the union-of-connected-subsets argument; component existence and equality of intersecting maximal connected sets are explicit: PASS.
- Step 10 checked against the unit section in the item statement and the component description from Steps 8–9; all three intersection clauses follow: PASS.
- New nodes: none; the item has no newly created node files to audit under B1–B7.

Changes made in this second reading:

- Made the base hypothesis self-contained by naming the structure morphism $B\\to\\operatorname{Spec}k$ and adding the affine-spectrum definition dependency; this preserves the imported “separated finite-type $k$-scheme” hypothesis exactly.
- Verified the worker’s relative-spectrum correction, all edge cases (field base, zero/one coordinates, disconnected base, nonaffine base, and empty source fibres), citations, duplicate searches, and route dependencies; no proof step required further repair.
