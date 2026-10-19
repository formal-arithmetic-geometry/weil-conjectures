# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-framed-projective-diagram-resolution.json`: item, split into ten proof steps; no statement change.
- `dag/nodes/sec-six-functors/lem-coef-split-functor-coend-filtration.json`: new statement-only node, unsplit; Mathlib searches found no match for the relative coend filtration.
- `dag/nodes/sec-six-functors/lem-coef-functor-coend-homotopy-prism.json`: new statement-only node, unsplit; Mathlib searches found no match for realization of a functor-valued combinatorial homotopy.
- `citations.json`: verbatim statement quotes for every citation in the item's steps, numbered 1–10.

The two new nodes have no proof, proof dependencies, or proof sketch in their statements. Their model-free hypotheses make them genuine categorical tools, strictly below both model-category conclusions of the item. Neither is the framed diagram theorem or one of its clauses relabelled. There are two new nodes and zero Mathlib leaves. Existing item metadata and previous searches are retained; new actual searches have been appended.

## Attachments

None. Read-only searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item tag, framed bar/projective frame terminology, cosimplicial and prism constructions found no declaration stating this theorem. The ring-localization projective-dimension hit and the split Milnor triangle hit concern different objects. The upstream master checkout was searched as reference material only; its sorry declarations would not count as proofs.

## Literature wanted

WANTED: Philip Hirschhorn, Model Categories and Their Localizations, §§16.4–16.5 and 19.2–19.4, for the item's historical source citation; the sandbox PDF is a scan with no extractable text and was not used as verified proof text.

WANTED: Mark Hovey, Model Categories, Propositions 5.4.1 and 5.4.3, Corollary 5.4.4, Theorem 1.2.10(iv), for the scalar frame argument and model-category detection of weak equivalences; readable PDF and extracted text are retained in this sandbox.

WANTED: Daniel Dugger, A Primer on Homotopy Colimits, §3.4 proof of Theorem 3.5, §§3.10–3.12 and §19, for the item and both new nodes; readable PDF and extracted text are retained in this sandbox. These sources are absent from the repository literature archive, which this worker cannot edit.

The proof is explicitly `proof_origin.by = agent`: Hovey supplies scalar frames, and Dugger supplies the skeletal-pushout and contraction patterns, but neither is being quoted as stating our functor-valued generalizations. No Stacks tag states these model-category or varying-functor results. No SGA source is used.

## What needed repair

The item was statement-only with no proof. Its source already describes an agent extension, not the literal assertion of Hirschhorn 19.3.1; this split makes that distinction explicit. In particular the projective weighted-coend theorem above this item is not cited: doing so would create an ancestor cycle. The existing realization contraction and tensor skeletal-pushout nodes assume a simplicial enrichment or chosen simplicial tensors. Those hypotheses are absent here. Replacing scalar frame tensors by such tensors would leave a gap, so the two missing categorical arguments were isolated without adding enrichment to the item.

The imported reverse numbering is retained. Appending the terminal object gives an INITIAL extra degeneracy in that numbering, not the terminal face identity from the forward bar. Step 6 writes the correctly reversed identities; it does not mix the two conventions. The resulting tensor weight is the ordinary standard simplex, as stipulated by the item.

No statement dispute was found. No chapter, unit, target, source checkout, repository file or launcher file was changed. This is an auxiliary node of the existing unit, not its statement-realizing node, so the unit's realized fields are not edited.

## Searches and duplicate checks

Before creation, searched the whole DAG for cosimplicial tensor/frame, framed bar, extra degeneracy, skeletal coend, projective resolution and prism terminology, and read the nearby node statements named below. Ran `tools/blueprint_refs.py ancestor` on the item and whole-blueprint searches for `cosimplicial`, `cosimplicial resolution`, `extra degeneracy`, `frame`, `bar`, `prism`, `skeletal filtration`, `split simplicial`, and `coend`. The broad words frame/bar return unrelated geometric nodes; the specific searches return no blueprint node stating either new lemma. The nearest blueprint ancestor and complete via chain are retained. All same_as lists are empty.

Actual Mathlib commands and their digests are in searches.jsonl; the node records copy the exact tool/query strings. Each new node has LeanSearch, LeanFinder with two different phrasings, Loogle, and a source grep. All these services answered successfully. Read Splitting in Mathlib/AlgebraicTopology/SimplicialObject/Split.lean:199–219: it defines the coproduct decomposition, not the relative weighted realization filtration. The semantic hits RelativeCellComplex.attachCells and SSet.skeleton construct cells or a simplicial subset, not a comparison with this coend. Read the combinatorial Homotopy structure at Homotopy.lean:49–76 and its functoriality; it does not give the coend prism. ExtraDegeneracy's homotopy equivalence result concerns alternating chain complexes; SSet.toTop and relative simplicial-set homotopies concern different target categories. For the item, CofibrantObjectHomotopy.lean:127–152 supplies an abstract cofibrant replacement and Reedy/Basic.lean:21–24 still lists the Reedy model structure as TODO. None is an attachment or one-line Mathlib specialization of the item.

## Not duplicates

lem-coef-split-functor-coend-filtration vs lem-coef-weighted-coend-skeletal-filtration: the existing result filters the r-direction pairing of one cosimplicial diagram with a simplicial presheaf; the new result filters the OUTER p-direction of a varying simplicial family of colimit-preserving functors applied to K times Delta^p, using its specified coproduct splitting. It is not obtained by setting J to a point in the existing statement.

lem-coef-split-functor-coend-filtration vs lem-coef-tensor-coend-skeletal-pushouts: the existing statement requires an enriched category and its chosen tensors of objects; the new one has no enrichment and allows the coefficient functor to vary with p. It also states the relative filtration for arbitrary K to L.

lem-coef-split-functor-coend-filtration vs lem-coef-free-bar-cell-filtration: the existing statement is a simplicial-set-valued free ordinary bar with its own filtration and contraction; the new statement has no category J, free diagram, model structure or bar, and treats arbitrary split simplicial families of left-adjoint-like functors into any cocomplete category.

lem-coef-functor-coend-homotopy-prism vs lem-coef-reedy-realization-prism: the existing result assumes a simplicial model category and uses its tensor of the realized object; the new categorical result realizes a homotopy of varying functors without any enrichment, model structure or cofibrancy and has domain R_T(K times Delta^1).

lem-coef-functor-coend-homotopy-prism vs lem-coef-simplicial-realization-extra-degeneracy: the existing result proves a model-category weak equivalence of the tensor realization of a Reedy-cofibrant simplicial object; the new result constructs a map from combinatorial homotopy data in a functor category, without any weak-equivalence assertion.

lem-coef-functor-coend-homotopy-prism vs lem-coef-simplicial-extra-degeneracy-prism: the existing statement produces the combinatorial homotopy; the new statement realizes an already specified homotopy by triangulating the weight. Both are needed in step 7.

## Review by N2

I read Hovey's proof of Proposition 5.4.1, the qualification before Proposition 5.4.3, and Corollary 5.4.4, printed pp.130–131. In particular I checked the qualification that an arbitrary Reedy-cofibrant cosimplicial object is not enough for the trivial-cofibration conclusion: the collapse weak equivalences are essential, and are present here because each A_j is a resolution. I read Dugger's actual skeletal square in the proof of Theorem 3.5, printed p.10, and the two extra-degeneracy conventions in Definition 3.11, printed pp.12–13. The categorical extensions are marked as such in the two new source fields. On checking the promised Appendix A, I found it contains only a placeholder: Proposition 3.12 calls its proof an exercise and points to that missing appendix. I removed that appendix as proof evidence. The categorical prism is consequently a new statement-only node, with its intended triangulation argument recorded here, rather than a claim that the source supplied missing details. The prism extension is the decomposition of Delta^p times Delta^1 into the p+1 standard prisms with vertex lists (0,0),...,(a,0),(a,1),...,(p,1). On that simplex use H_a^p followed by the U coend map. The adjacent-prism faces agree by the middle homotopy identity, the remaining faces by the other face identities, and degeneracies by the degeneracy identities. Colimit preservation is precisely what lets the coefficient functor carry this decomposition to C. This is a separate categorical lemma, not hidden in a long proof step.

For the new filtration statement I checked the relative skeletal square in the functor category: the degeneracy splitting removes the latching summands, leaving N_p on the union (L times boundary) union (K times simplex). Its argument is a general coend calculation, not an elementary two-line consequence of the existing differently typed tensor statement. The new statement includes the canonical splitting map, the coequalizer relations, the attaching map, p=0, and the colimit. No geometric or homotopical hypothesis has been smuggled into it.

Step 1 uses the actual latching-object definition and cofibration test in lem-coef-reedy-model-structure. It proves the co-Yoneda and boundary identifications by their cocones rather than citing a definition node for a theorem. Step 2 uses exactly the preservation conclusion of lem-coef-simplicial-boundary-collapse-test, after verifying every hypothesis in step 1.

Step 3 constructs the splitting required by the new filtration node. I checked identity deletion for length zero, for all-identity chains, and for a pair of inverse nonidentity arrows: the latter stay nondegenerate even if their composite is identity. No assumption that J is direct, skeletal or loop-free occurs. The free-diagram formula and its action are explicitly written.

Step 4 uses exactly the displayed relative cells of lem-coef-split-functor-coend-filtration. It writes the union defining b_{n,p}, checks injectivity degreewise, and proves preservation by F_c by its evaluation/coproduct lifting bijection; this last fact is a short explicit argument, not a new node. Step 5 uses the pushout clause of lem-coef-lifting-class-closure and the continuous ordinal-composite clause of lem-coef-transfinite-left-lifting. Their statements say these closure properties, and projective cofibrations are the requisite left class because the projective model structure is a hypothesis, not a theorem invoked for arbitrary M. The Reedy criterion is the statement of lem-coef-reedy-model-structure. All these cited nodes were opened and read.

Step 6 is the explicit initial extra-degeneracy verification with the reversed faces, and needs only the displayed definitions and the functoriality of A. Step 7 uses exactly the section and combinatorial homotopy clauses of lem-coef-simplicial-extra-degeneracy-prism, applied in a functor category, then exactly the map and endpoint clauses of lem-coef-functor-coend-homotopy-prism. I checked the target identification for a constant coefficient functor by commuting its colimit with the constant-coefficient simplex coend. The augmentation obtained this way is the collapse/composition augmentation in the statement, not a replacement chosen after the fact.

Step 8 uses the actual horn/trivial-cofibration and lifting descriptions of lem-coef-kan-quillen-right-proper, the anodyne pushout-product statement of lem-coef-sset-anodyne-pushout-product twice, and the same new filtration and two lifting-closure nodes as steps 4–5. Those statements give precisely the relative cells and weak-factorization closure used here. This proves the cylinder projection is weak by two-out-of-three; it does not assume realization preserves objectwise weak equivalences, nor that M is simplicial or proper. Step 9 uses exactly the iff clause of lem-coef-model-localization-detects-weak-equivalences: the prism makes the augmentation invertible after localization, and that cited statement requires no cofibrancy/fibrancy. Step 10 writes the augmentation naturality equation and applies the weak-equivalence axiom from lem-coef-reedy-model-structure. Its empty-J check is explicit.

Every proof citation is backed by a verbatim quote in citations.json. All cited proof nodes belong to the same unit or are existing Mathlib tools; no off-route replacement or unrecorded tool edge is needed. All ten steps are below 2000 characters, and the two genuine categorical sublemmas have been extracted rather than hidden inside a long step.

I tested the new filtration at p=0 (boundary empty), K=L (all transitions identities), K=L=empty (all terms initial), and a constant T with N_0=T and all higher N_p initial (only the degree-zero transition remains). This also checks that no hidden nonempty indexing hypothesis is needed. For the prism, constant T,U reduce to equal endpoint maps because the homotopy identities force f=g; K=empty has initial source and target; p=0 is just the usual edge with its two stated endpoints. For the item, J empty is terminal-diagram vacuity, J terminal reduces to the scalar frame, and a discrete J has no nonidentity bar cells. None requires an enrichment, a combinatorial hypothesis, or properness. No new assertion failed these checks.

## Unfinished work

The two new statements are deliberately left unsplit, as required for a one-level stage-1 delivery. No Lean code or compilation is part of this work. Final acceptance is the independent maintainer's review after the required server dry run and push.
