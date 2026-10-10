# Stage-1 split: lem-exc-etale-sheaves-gsets-point

## Files written

- dag/nodes/sec-curve-estimates/lem-exc-etale-sheaves-gsets-point.json: split item, four proof steps.
- dag/nodes/sec-curve-estimates/lem-exc-field-sections-stalk-invariants.json: new statement-only node; no Mathlib match. LeanSearch returned HTTP 500; LeanFinder and source grep found none.
- citations.json: one verbatim statement quote for each cited node at each proof step.

## Attachments

None. The slopmaster2 source has no declaration tagged lem-exc-etale-sheaves-gsets-point, and searches of its algebraic-geometry source found no declaration stating the set-valued equivalence.

## WANTED

literature/stacks-project/etale-cohomology.tex, Tags 03QW, 03QT, 04JM, for this item and the new node. The literature checkout is absent on this machine. I read the corresponding Stacks pages at https://stacks.math.columbia.edu/tag/03QW, https://stacks.math.columbia.edu/tag/03QT, and https://stacks.math.columbia.edu/tag/04JM, and wrote the omitted full-faithfulness details as an agent proof.

## Correction

The imported statement called Spec K^sep a geometric point. For imperfect K, K^sep need not be algebraically closed, whereas [def-weil-geometric-point] requires an algebraically closed residue field and Stacks 03QT assumes a geometric point. I replaced it by Spec Omega for an algebraic closure Omega containing K^sep. The represented stalk remains Hom_K(Spec K^sep, X) because an etale K-scheme is a disjoint union of finite separable field spectra. No conclusion was weakened.

## Review by G1

I read Stacks 03QW (the action formula and open stabilizers), 03QT (the sheaf/G-set equivalence and its representable inverse), 04JM (the direct descent proof of the section/invariant formula), 03QR (etale K-schemes and discrete G-sets), and 03PC (decomposition of an etale K-scheme). The item agrees with 03QT after correcting the geometric point. The new node specializes the direct proof in 04JM from K to each finite separable L/K; its statement includes the action formula for every K-embedding, which follows by evaluating at the chosen lift and extending that embedding to a member of G.

For step 1, [def-weil-pbc-geometric-stalks] supplies triples indexed by pointed neighbourhoods and [lem-weil-pbc-etale-fibre-discrete-separable-points] supplies finite separable residue fields. Thus automorphisms fixing K^sep act trivially on each triple, and the finite residue field gives an open subgroup fixing it. I checked that an automorphism of K^sep extends to Omega and that the resulting action is independent of the extension. These are the exact hypotheses in the cited statements.

For step 2, [lem-weil-pbc-small-etale-representable-presheaf-sheaf] says h_X is a sheaf, [lem-galois-stalk-representable] says its geometric stalk is the set of Omega-points, and [lem-weil-pbc-etale-fibre-discrete-separable-points] says each component is the spectrum of a finite separable field. Any embedding of that field into Omega lands in K^sep, proving the asserted bijection, also when X is empty. None of these citations is merely a definition offered for a theorem.

For step 3, the new node states exactly the needed bijection F(Spec L) = M^{H_L}, natural under all K-embeddings L to L', as well as sheaf morphisms. The etale-fibre node supplies the coproduct decomposition of an arbitrary object of the site. The sheaf condition for that coproduct reduces sections to products. The action formula in the new node makes the maps induced by a G-equivariant M to N natural under arbitrary maps of components, so they assemble into a sheaf morphism and recover the original map on stalks. I corrected an earlier draft which only asserted compatibility for inclusions L subset L'; that was insufficient for full faithfulness.

For step 4, [lem-exc-etale-field-gsets] states the equivalence producing X from any discrete G-set M. The representable-sheaf, stalk, and etale-fibre nodes used again in the text of step 2 state precisely why h_X has stalk M. This proves essential surjectivity without asking the etale-scheme node to imply a sheaf equivalence.

I checked B1-B10: the new node has only a self-contained statement with its field, closure, point, site, sheaf, and subgroup introduced; its TeX has one rendered backslash; the source uses Stacks tags and labels; it is not marked a Mathlib leaf. A whole-DAG search for 04JM and the section formula, plus blueprint searches for "sections over finite separable" and "invariants", found no blueprint node with this set-valued formula. Existing lem-exc-field-discrete-modules is about module sheaves and cites this item, so it cannot be used here. The new node comes from the third paragraph of its nearest blueprint ancestor. C1-C8: every non-elementary fact in the item is stated by a cited node, every quote in citations.json occurs verbatim in that statement, and no cited node depends on this item. The etale-fibre decomposition and representable-sheaf facts are generic tools from another unit, declared in split_report.tool_uses.

For E1-E6, I tested K separably closed (G trivial; the section formula is F(Spec K)=M), L=K (invariants under G), L/K finite Galois (H_L normal and the formula respects conjugation), and the empty X and empty sheaf (all relevant Hom and stalk sets empty). The proof uses no finite-type or quasi-compact assumption on X; the etale-fibre node allows arbitrary disjoint unions. The item correction above addresses the false geometric-point hypothesis rather than silently changing its meaning. The Stacks proof says "details omitted" at the representable-stalk identification; step 2 supplies them from cited nodes. No source error remains.

No part of this split remains unfinished; the new statement-only node is intentionally left for a later stage-1 worker.
