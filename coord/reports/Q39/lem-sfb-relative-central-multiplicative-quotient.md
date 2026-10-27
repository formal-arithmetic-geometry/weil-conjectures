# Q39: lem-sfb-relative-central-multiplicative-quotient

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-central-multiplicative-quotient.json`: item, now split; statement retained, eleven explicit proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-affine-multiplicative-quotient.json`: statement-only prerequisite; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-central-multiplicative-preimage.json`: statement-only prerequisite; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-torus-automorphism-fixed-group.json`: statement-only prerequisite; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-equivariant-quotient-fixed-surjectivity.json`: statement-only prerequisite; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fibral-isomorphism-flat-source.json`: statement-only prerequisite; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-field-reductive-quotient.json`: statement-only prerequisite; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-connected-multiplicative-torus.json`: statement-only prerequisite; no Mathlib match.
- `citations.json`: exact statement quotations for every step-node pair.
- `searches.jsonl`: actual search-command results, retained unchanged.
- `report.md`: this report. `prepare.py` is sandbox-only preparation code, not a library or tooling change.

## Attachments

None. Searched the project Lean source under `lean/WeilConjectures/` for the item blueprint tag and the notions central quotient, reductive group, multiplicative type and maximal torus, also inspecting the adjacent `lean/Sheaf/` source. There is no project declaration giving all clauses with a finished proof. Abstract-group centres and special-linear-group pointwise centres are not this group-scheme assertion. No Lean was written or compiled.

## Literature wanted

WANTED: `literature/conrad-reductive-group-schemes.pdf`, Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Lemma 3.3.1(2), Lemma 3.3.2, Theorem 3.3.4 and Corollary 3.3.5, printed pp.96–101, for the item and the affine quotient and central-preimage prerequisites.

WANTED: the same document, Lemma 2.2.4 and Example 2.2.6, printed pp.65–67, the paragraph preceding Remark 3.1.5, printed p.83, and Corollary 3.3.5 proof, printed p.101, for the torus automorphism fixed-group and equivariant fixed-surjectivity prerequisites.

WANTED: the same document, Lemma B.3.1, printed p.288, for the fibral isomorphism criterion; Proposition B.3.4 and the character description of tori for the smooth connected multiplicative-type recognition prerequisite; Section 1.1 adjacent to Definition 1.1.11, printed pp.10–11, for preservation of reductivity by surjective homomorphisms.

I read these places in the online PDF. No literature was downloaded or written into the repository. As this reference is not locally archived, the assembly has `proof_origin.by = agent`. No SGA source is used. Stacks 039C, in the local more-morphisms chapter, was checked as a flatness criterion; it is not misrepresented as a complete fibral-isomorphism theorem. No Stacks tag was found for the reductive structural statements themselves, so their exact Conrad references are retained.

## What was wrong and what was retained

The supplied node was an unsplit statement with no proof, not a disputed or false statement. There is no statement correction. In particular, I retained scheme-theoretic kernels and inverse images, nonsmooth multiplicative kernels, and arbitrary base change. Replacing them by algebraically closed points would lose information in characteristic p.

The latest blueprint is `literature/blueprint/latest/`, including `blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, proof (3). I read its direct-image route and the item chapter/unit records. This is a structural tool deep in the existing alteration/moduli prerequisite chain, not a replacement route for that unit. `blueprint_refs.py ancestor` reports no imported blueprint ancestor: the inherited `from.node = null` is preserved, along with its long specific place and via list, and the item is prepended to the new nodes' via lists. Whole-blueprint searches found no equivalent imported node. I did not invent an ancestor or edit a unit that this item does not realize directly.

## Mathlib and duplicate searches

Read the inherited Q97 searches and kept them. Every new search was executed through `msearch.py Q39 lem-sfb-relative-central-multiplicative-quotient`; exact query strings and returned result records are in the nodes and the command's log. Each new node has LeanFinder, Loogle, grep and LeanSearch results, with a second semantic phrasing. The grep searches concern the relevant AlgebraicGeometry directory. Searches found abstract quotient groups, representation fixed points, topological tori and generic smooth/flat scheme facts, not these statements.

For the one potentially close generic criterion, I inspected the reported Mathlib flat-monomorphism declarations: `AlgebraicGeometry.Flat.isIso_of_surjective_of_mono` assumes flatness of the map being proved an isomorphism, whereas the new lemma assumes flatness of X over a third base S and obtains the map's properties from fibres. The former is not a one-line specialization of the latter. Fibre-product and affine-group fibre isomorphism hits likewise do not imply the general criterion.

Before writing new nodes I searched the entire DAG statements and source references for normal affine quotients, central multiplicative preimages/extensions, torus centralizers and actions, reductive quotients, fibrewise isomorphisms, and smooth connected multiplicative-type groups, and used `tools/blueprint_refs.py search`. The existing node statements used by the proof were opened in full. In particular, the centre-weight node's first assertion and base-change clause really state the centre theorem; the character-duality node really states quotient by D(M/L), not just full faithfulness; and the field self-centralizer theorem includes nonreduced test algebras.

## Not duplicates

- lem-sfb-relative-affine-multiplicative-quotient vs lem-sfb-affine-normal-quotient-geometry: the existing node is over a field and allows arbitrary affine normal kernels; the new node is over every scheme, for multiplicative-type normal kernels, and includes affine representability with arbitrary base change.
- lem-sfb-relative-affine-multiplicative-quotient vs lem-sfb-relative-central-multiplicative-quotient: the new prerequisite has no reductivity, centre identification or torus correspondence. It is the independent smooth connected affine quotient construction used twice, including for the fixed group, not a renamed reductive conclusion.
- lem-sfb-relative-central-multiplicative-preimage vs lem-sfb-multiplicative-extension-action-rigidity: the latter is an algebraically closed-field action-rigidity assertion, not the relative scheme-theoretic central and multiplicative preimage theorem.
- lem-sfb-relative-central-multiplicative-preimage vs lem-sfb-commutative-multiplicative-type-extension: the existing node assumes commutativity and an algebraically closed field; the new node must prove centrality and multiplicative type of the preimage over any base.
- lem-sfb-relative-torus-automorphism-fixed-group vs lem-sfb-relative-torus-centralizer-normalizer: the existing statement concerns an embedded split torus and does not assert connectedness or reductivity of the centralizer. The new theorem treats arbitrary torus automorphisms, including the action obtained from the quotient, where the acting torus is not a subgroup of G.
- lem-sfb-relative-torus-automorphism-fixed-group vs lem-sfb-torus-centralizer-smooth-connected: the existing theorem is over a field, for a torus subgroup; the new one is relative, for an automorphism action, and includes reductivity and arbitrary base change.
- lem-sfb-relative-torus-automorphism-fixed-group vs lem-sfb-reductive-torus-fixed-subgroup: the existing theorem has an algebraically closed field and a torus embedded in the reductive group, rather than an arbitrary relative torus action.
- lem-sfb-torus-equivariant-quotient-fixed-surjectivity vs lem-sfb-relative-torus-automorphism-fixed-group: smooth representability of fixed groups does not imply right exactness for an equivariant surjection. The new theorem is the separate field lifting input used on each geometric fibre.
- lem-sfb-fibral-isomorphism-flat-source vs lem-sfb-fibrewise-flatness-criterion: the existing theorem concludes flatness at a point, not a global isomorphism from isomorphisms of all geometric fibres.
- lem-sfb-fibral-isomorphism-flat-source vs lem-sfb-surjective-flat-closed-immersion-isomorphism: the existing theorem requires a flat closed immersion; the new theorem has only an S-morphism with flat source over S and fibre isomorphisms.
- lem-sfb-field-reductive-quotient vs lem-sfb-reductive-radical-quotient: the existing statement concerns a specific radical quotient, while the new theorem concerns arbitrary faithfully flat homomorphisms with smooth connected target, including noncentral and nonsmooth kernels.
- lem-sfb-smooth-connected-multiplicative-torus vs lem-sfb-multiplicative-type-largest-subtorus: the latter is field structure theory for the largest subtorus, not a torus-recognition theorem over arbitrary, possibly nonreduced, schemes.
- lem-sfb-smooth-connected-multiplicative-torus vs def-sfb-tori-multiplicative-type: the existing node defines field tori and multiplicative type; a definition does not prove the relative smooth-connected recognition criterion.

- lem-sfb-fibral-isomorphism-flat-source vs lem-sfb-fibre-flatness-compatible-stalk-data: the existing node identifies compatible stalk and fibre rings and their finiteness properties; it concludes no isomorphism of schemes.
- lem-sfb-fibral-isomorphism-flat-source vs lem-sfb-fibrewise-module-flatness-criterion: the existing node concludes stalk-module flatness and target flatness at a point from module-flatness hypotheses; it does not give a global isomorphism criterion.
- lem-sfb-fibral-isomorphism-flat-source vs lem-sfb-relative-flat-fibre-test: the existing node detects flatness of f on fibres with a flat source; the new node concludes that f is an isomorphism from geometric fibre isomorphisms, and still requires the separate etale/radicial and global identification argument supplied by Conrad B.3.1.

## Review by Q39

I checked the split against delivery-errors B–E with the cited statements open. The item is the exact source conclusion of Conrad Corollary 3.3.5, supplemented by the represented fppf quotient's torsor description. I read its proof, Lemmas 3.3.1–3.3.2 and the centre theorem immediately before it. The seven new prerequisites are genuine general inputs: affine quotient existence without reductivity; relative extension/preimage rigidity; fixed groups for torus automorphisms; right exactness of the fixed-group construction over a field; the general fibral isomorphism criterion; reductivity of smooth connected quotient groups over a field; and recognition of relative tori among multiplicative-type groups. Their statements introduce their own objects and have no proof steps; they are queued for splitting. The item does the actual centre identification and constructs both directions of its torus correspondence rather than delegating them to newly renamed clauses.

Step 1 uses precisely the affine quotient existence theorem and the field reductive-image theorem. Central C is normal; G has connected geometric fibres; multiplicative type includes finite presentation; geometric fibres of the quotient map remain faithfully flat. Both source and target on those fibres are smooth connected affine finite-type groups. The field image theorem has no separability condition on the kernel, which matters here.

Step 2 uses the quotient prerequisite's kernel and torsor clauses. I wrote the inverse (g,h) ↦ (g,g⁻¹h) and checked it on all test schemes. Step 3 uses the existing relative centre statement for G and Q over the original Noetherian affine base, and the central-preimage theorem with D=Z(Q). Its hypothesis is centrality of D in Q, not just commutativity. The reverse inclusion is proved using fppf lifts of arbitrary points, so equality is scheme-theoretic; local lifts also prove the quotient identification, with no claim of surjectivity on every set of rational points.

Step 4 combines the torus-fixed representability theorem, the existing field self-centralizer theorem, and the fibral isomorphism criterion. The source torus is smooth and flat over S. All fibres are geometric fibres, where maximality is part of the item's definition. This short comparison is written out and does not assume that pointwise equality detects nilpotents. It applies to Q as well.

Step 5 uses the exact closed-immersion and quotient assertions of the existing relative character-duality statement, plus the existing finite-free-subgroup theorem (declared as a generic off-unit tool). Simultaneous fppf splitting is obtained by refining the covers which split T and C; the character map is locally a surjection M→N. Its kernel L is a subgroup of a finite-rank lattice, so D(L) is a torus. The map into Q is monic by explicit local lifts, and the existing multiplicative-type monomorphism theorem gives a closed immersion. I checked that theorem allows torsion and arbitrary bases. The inverse-image calculation is another explicit local-lift argument, not an unquoted subgroup-correspondence theorem.

Step 6 proves maximality of T/C using the field equivariant fixed-surjectivity theorem. Centrality of C makes the quotient conjugation action well-defined even on nonreduced test schemes. The action on C is trivial, so the fixed kernel is exactly C, and the fixed quotient is the centralizer of R. A torus containing R centralizes it, which finishes the geometric maximality test. This replaces an unexplained invocation of classical maximal-torus image theory with the cited fixed-group statement.

Step 7 uses the relative fixed-group theorem for the action of U on G, not an embedded-torus centralizer statement. Its reductivity clause gives H reductive and its connected-fibre clause permits a second use of the affine quotient theorem. Step 8 uses field fixed-surjectivity and the base-change clauses of both prerequisites to identify the geometric fibres of j. H/C is flat because it is smooth, and both source and target are locally finitely presented over S, exactly as required by the fibral isomorphism criterion. I then give the all-test-schemes lifting proof that H is the entire inverse image of U.

Step 9 applies the central-preimage theorem to H→U, not directly to the nonsmooth inverse image before its smoothness has been proved. Here D=U is central in itself and multiplicative. The theorem makes H itself multiplicative type. The smooth-connected recognition theorem then gives that H is a torus; merely saying H is commutative would not suffice. I read its character-sheaf criterion in Appendix B and retained connectedness of every whole geometric fibre, essential to excluding finite étale factors. Step 10 is only the written three-line maximality and inverse-map argument from earlier steps, so it is elementary, with no new node for it.

Step 11 uses each cited theorem's actual arbitrary-base-change clause. The centre theorem is first applied over the original Noetherian affine base; its base-change conclusion, rather than an illicit new application over a non-Noetherian base, handles an arbitrary S′. Quotients and inverse images are identified as sheaves and fibre products. Maximality is geometric and can also be tested by the established self-centralizer equality. The correspondence is natural under pullback; no assertion that every torus after base change descends has been made.

I tested the assertions with the trivial group and rank-zero torus, C=1, G a torus with C=G, a finite étale multiplicative kernel, and C=μ_p in characteristic p (including central μ_p in SL_p). The torsor formulas still hold for infinitesimal sections. Frobenius on G_m is a test of the field fixed-surjectivity statement with nonsmooth kernel; it must be faithfully flat, not smooth. A trivial torus action fixes the entire group, as required by the fixed-group statement. Nonreduced bases, such as Z/p²Z, are allowed by the quotient and character criteria; the fibral criterion retains flatness of its source and does not infer an isomorphism from fibres alone. Disconnected smooth diagonalizable groups are excluded by the recognition lemma's connected-fibre hypothesis. Every proof step is below 2000 characters; the longest is under 1000. There is no long inline structural lemma, hidden finite-cover assumption, SGA route, silent target weakening, or new elementary/restatement node.

The main corrections made while assembling the proof were to distinguish an arbitrary automorphism action from an embedded split torus; to separate smoothness of the quotient map from faithful flatness; to use a genuine flat-source fibral-isomorphism theorem rather than a flat-monomorphism theorem with missing hypotheses; and to retain all-test-scheme rather than pointwise equalities. Exact statement quotations for all citations are in citations.json.

## Unfinished work

No unfinished assembly step. The seven new statement-only prerequisites are intentionally unsplit, as required for a one-level stage-1 delivery. No new Mathlib leaf is claimed; one existing Mathlib leaf is reused. Required server dry run and delivery are performed after writing this report.

The first dry run identified three additional 039C-tagged nodes. I opened each complete statement: compatible stalk data gives local ring identifications; module flatness gives stalk flatness; the relative fibre test gives flatness of f, not its being an isomorphism. Added the three precise nonduplication comparisons above; the general isomorphism criterion remains a distinct prerequisite.

The second dry run found that grouped notion references were not recognized by preflight on two new statements. Expanded all new-node grouped references to individual [id] citations without changing their mathematics or dependencies, and regenerated their exact citation quotations.
