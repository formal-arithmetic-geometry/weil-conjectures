## Worker report

Files written in dag/nodes/sec-six-functors-basics/:
- lem-sfb-space-qc-open-schematic-closure.json: item split in seven steps, statement unchanged.
- lem-sfb-space-ideal-closed-subspace-correspondence.json: new statement-only lemma, unsplit; no Mathlib match.

Also wrote citations.json (18 verbatim quotations, one for each step/node citation) and retained searches.jsonl. Attachments: none. WANTED: none. Nothing remains unfinished in this one-level split. There are no Lean edits or compiler invocations.

The imported item had no proof. Its Mathlib searches identify only scheme constructions. I searched the upstream WeilConjectures and Sheaf sources by the exact blueprint tag and the schematic-image/closure terminology: no project declaration proves the algebraic-space statement, so ATTACH does not apply. The existing stack schematic-image node is a much stronger, unsplit stack theorem; using it would obscure the elementary open-immersion kernel argument. The new node is the general ideal-to-closed-subspace correspondence, not a closure clause moved out of the item.

## Source and blueprint searches

Read spaces-morphisms.tex, Tags 082X (lemma-scheme-theoretic-image), 082Z (lemma-quasi-compact-scheme-theoretic-image), 0836 (lemma-characterize-scheme-theoretically-dense), and 03MB (lemma-closed-immersion-ideals), including the paragraph after definition-inverse-image-closed-subspace. Read the chapter and unit DAG records and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This supplies a geometric prerequisite to the inherited 09YB route, not a change to the unit or chapter. The ancestor tool returns None; the inherited from.node and via chain have been retained and the new node prepends this item to via.

Before creating the node I searched all dag/nodes for 03MB, 082X, 082Z, closed subspace, quasi-coherent ideal, correspondence, kernel and scheme-theoretic image; read the matching node statements; and ran blueprint_refs.py search for schematic closure, scheme theoretic image, quasi-coherent ideal, closed subspace and 03MB. There is no blueprint statement giving the algebraic-space correspondence. The scheme-only Nagata image and ideal records cannot supply it for arbitrary spaces.

Ran msearch.py for the item and the new node, with two semantic phrasings for the new node, Loogle, LeanSearch and grep, preserving the actual log records in each node. All services answered. Read the scheme-only candidate sources: Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:180 (overEquivIdealSheafData) and Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:454 and :472 (subscheme and subschemeι). Their domain is Scheme, so none is an exact or one-line algebraic-space specialization. No Mathlib leaves were created.

## Not duplicates

lem-sfb-space-ideal-closed-subspace-correspondence vs lem-sfb-space-closed-immersion-quasi-coherent-modules: the existing statement gives the ideal and module embedding for an already supplied closed immersion; it does not construct the closed subspace from an arbitrary quasi-coherent ideal or state the converse bijection, zero-pullback factorization criterion, or base-change ideal formula. Only that missing correspondence is added, rather than a duplicate of its module-equivalence theorem.

lem-sfb-space-ideal-closed-subspace-correspondence vs lem-sfb-space-stalk-ideal-pullback: the existing statement assumes a commutative square of square-zero closed immersions and computes its stalks and cartesian criterion; it does not construct a closed subspace from an arbitrary quasi-coherent ideal, and imposes square-zero hypotheses absent from the new statement.

## Review by Q16

I read the item against 082X and all four clauses of 082Z and checked the conclusion clause by clause. The statement has not been corrected or weakened: B need not be quasi-separated, Noetherian, or reduced; quasi-compactness belongs to j. I read the new node against every assertion of 03MB and the following inverse-image paragraph. The algebraic-space-source factorization criterion is expressly in the source statement. Its equivalent direct-image form is the tensor-pullback/direct-image adjunction, which the statement cites. The statement specifies its ambient scheme, universes, module categories, ideals, representable closed immersions and all maps. It contains no proof or hidden data choice, and remains unsplit.

Step 1 uses the actual direct-image assertion of lem-trf-space-qc-separated-quasi-coherent-pushforward with F = O_O, and the kernel assertion of lem-sfb-space-qcoh-kernels-colimits. I checked the separated hypothesis: an open subfunctor is monic, so its diagonal is an isomorphism and is closed on every scheme test. No separation of B is used. The new node supplies the construction V(I), which the existing forward-only 03MB node does not supply.

Step 2 uses the new node's zero-map factorization criterion and its inclusion-reversing bijection. The inclusion J contained in I is a literal kernel inclusion, so it proves minimality without assuming a factorization from point-image containment.

Step 3 uses exactly the sectionwise, restriction-compatible comparison of lem-trf-space-etale-module-pushforward-restriction and the new node's base-change ideal formula. The two structural ring maps agree under that comparison; their sectionwise kernels therefore agree. The quasi-compactness of j after each test follows because the same test is a test into B. For open restriction I wrote the same full-subsite kernel argument directly, rather than citing an étaleness definition as a theorem about open immersions.

Step 4 identifies C times_B O with O using the zero ideal on O. This is a cartesian identity of subfunctors, so the induced factor is a quasi-compact open immersion on every scheme test. The elementary mark covers this explicit base-change argument from the definitions already cited.

Step 5 reapplies the same two quasi-coherence results to q, whose quasi-compactness and separatedness have now been checked. The new node constructs D from the actual kernel on C. The composite D into B is closed by the successive-quotient calculation written in this step and the affine-quotient clause of def-weil-closed-immersion. Minimality forces D = C, and the bijection forces its kernel to be zero. Thus schematic density is proved and not silently inferred from mere topological density.

Step 6 uses def-trf-algebraic-space for the atlas and structure-sheaf values; lem-a1-space-point-open-calculus for open-subspace topology and the point image of the fibre product; and the explicit direct-image section formula in lem-trf-space-etale-module-pushforward-restriction. I checked that a nonempty affine chart can be chosen over the putative open complement and that its pullback of O has empty point set and hence is the empty scheme. The injection into the zero ring then contradicts its nonemptiness. This step is marked non-elementary because it cites the atlas point calculus, although its remaining ring argument is immediate.

Step 7 is the elementary two-inclusion argument for the closed restriction; Step 3 identifies the correct schematic closure, and the given closed subspace itself is a competitor. No radical or reduced-induced structure is substituted.

I tested the new correspondence on the zero ideal (whole space), the unit ideal (empty subspace), and a nonradical ideal (Spec k[epsilon]/epsilon^2 with the ideal (epsilon)); the factorization criterion is scheme-theoretic, not just set-theoretic. For the item, O empty gives the empty closure, O = B gives B, a clopen O gives C = O, and a dense principal open in a nonreduced affine keeps precisely the kernel-supported scheme structure. No finiteness of the ideal is assumed. Every non-elementary fact is a cited statement; all 18 quotes are verbatim substrings. The longest proof step is under 900 characters, so no step crosses the 2000-character hidden-lemma threshold. Source is Stacks only, with no SGA. The three off-unit nodes are generic module-localization, quasi-coherent-pushforward and atlas-point tools, declared in split_report.tool_uses for maintainer review; they do not replace any unit route. I corrected only the proof's citation of open restriction and added the point-calculus citation during this reading.
