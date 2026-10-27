# Stage-1 report: lem-sfb-simplicial-simplex-copower-contraction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-simplicial-simplex-copower-contraction.json: item, statement unchanged, four-step split; not a Mathlib leaf.
- citations.json: one verbatim statement quote per step/node citation.
- searches.jsonl: six actual searches from msearch.py, all services available this time. The seven inherited O1 search records are preserved in the item, including the explicitly unavailable historical LeanSearch result.

No new nodes and no new Mathlib leaves. No Lean files, compiler, Lake, build, repository git, or repository writes.

## Attachments

None. Searched the project WeilConjectures tree for the blueprint tag and for simplex/copower/contraction combinations, then read the likely algebraic-topology and category-theory hits. There is no project declaration stating all clauses of this item. The generic Mathlib homotopy conversion does not assert the needed copower augmentation.

## WANTED

None. All sources needed for this split are present locally.

## What was wrong or missing

The imported item had a correct statement but no proof. The source's claim that the coefficient-copower construction carries simplex contractions to homotopy equivalences needed the explicit coefficient formula and verification; a bare claim of functoriality would hide its compatibility with the varying groups A_n. Steps 1 and 2 now provide that verification. No statement dispute or correction was needed.

The inherited blueprint ancestor is null because its provenance eventually reaches created.item = Sheaf.SixFunctors.CtfStabilityDirectImages, which is a module rather than a DAG node. tools/blueprint_refs.py ancestor confirms null. As in the reviewed parent's report, I retained that provenance rather than fabricating an ancestor. I read the latest blueprint's sk-thm-sf-ctf-stability unit and det-thm-sf-ctf-stability-direct-images statement/proof (latest commit 7284bb09daf97437d544c51882b325f9c52cd345). Proof (3) now uses proper image, the open case and compactification. This split is the inherited homological input to its older alteration/cotangent chain; no unit/chapter route is changed. The blueprint searches for copower, simplex contractible, homotopy-s-N, and simplicial abelian found no imported blueprint statement of this item.

## Unfinished work

None within this one-level split. The general homotopy-equivalence-to-quasi-isomorphism theorem is reused as an existing DAG node and is not re-proved or restated here.

## Not duplicates

No new-node pairs exist. Related existing statements were read before deciding to reuse rather than create:

- lem-trf-simplicial-abelian-set-homotopy-quasi-iso is the general implication used in Step 3. It assumes an underlying homotopy inverse, which Steps 1 and 2 construct here; it is not this copower assertion.
- lem-weil-pbc-simplicial-homotopy-free-chain-homotopy concerns free modules on simplicial sets with a fixed coefficient ring. It does not cover the varying coefficient group A_n without a further construction.
- lem-sfb-poset-weak-prism-identity and lem-sfb-poset-augmented-chain-prism concern constant-coefficient poset chain complexes, respectively weak tuples and strict tuples with a degree-minus-one augmentation. This item concerns unaugmented alternating complexes with arbitrary simplicial abelian coefficients. Neither states its conclusion.

## Review by Q27

I read Stacks sites-cohomology.tex Tag 08RX, lemma-O-homology-qis, in full around its coefficient-copower argument. It explicitly applies a contraction of S to the copies of P_n and then to P'_n. I read simplicial.tex Tag 08Q3, example-simplex-contractible, including its warning that the chosen endpoint must be the last vertex for the displayed homotopy direction. The step uses exactly that last vertex, so the piecewise ordinal map is monotone. I also read Tag 019S and the chain-homotopy calculation surrounding it to check the advertised route, and Tag 08P2, lemma-homotopy-equivalence, in full as the source of the already existing theorem actually cited in Step 3. No SGA source is used.

Step 1 uses the statement of def-weil-pbc-simplicial-object: a morphism commutes with all simplicial operators. I checked this for both the constant-last-vertex inclusion and summation, obtaining epsilon i = id without any flatness or constancy assumption on A.

Step 2 uses def-weil-pbc-simplicial-set, whose statement defines natural simplicial maps, ordinal operators, and termwise elements. The entire contraction is written down, rather than cited as a new assertion. At a fixed parameter beta the map is additive; repeated target indices add, so it descends from summands to the direct sum. Precomposing the piecewise ordinal map equals taking the same piecewise rule after precomposition. Since every A(phi) is additive, that equality proves naturality even when indices collide. The endpoint beta=0 gives the identity and beta=1 gives i epsilon. All sums are finite, even without using the finiteness of the ordinal hom-set. This is a direct formula check, not an omitted prism lemma.

Step 3 uses the full statement of lem-trf-simplicial-abelian-set-homotopy-quasi-iso, which I opened and read. Its source objects are simplicial abelian groups, its f is additive, and its inverse and homotopies may be underlying simplicial-set maps. Our epsilon is additive by construction, Ui is a simplicial-set map, and Step 2 and epsilon i = id give precisely its two required homotopies. Its nonpositive cochain convention agrees word for word with this item; positive degrees are zero. No identification of normalized/free homology is borrowed from its proof. The second citation, def-weil-abstract-derived-category, explicitly defines D(A) as localization at quasi-isomorphisms; thus invertibility follows from what the cited statement says. This off-unit general homological theorem is declared in split_report.tool_uses; it replaces no geometric step of the unit.

Step 4 again cites def-weil-pbc-simplicial-object, for the operator compatibility of u. I checked each equality on e_alpha(a), so naturality applies to every simplicial morphism and does not depend on choosing a homotopy naturally. The inverses of the invertible augmentation square are natural by composing that equality on its two sides.

Edge cases: m=0 gives exactly one summand in each degree, so epsilon and i are identities. For A=0 every displayed map is the unique zero-group map, which is the identity on that object. Constant A is included but never assumed. In degree zero, the parameter has exactly the two constant endpoints, and the same formulas give x and i epsilon(x); there is no missing negative chain term. Noninjective ordinal operators may merge indices, which is why additivity was included explicitly. The statement requires m>=0, so the unavailable vertex of an empty simplex is never used.

I checked delivery-errors B--E against the written node: no unsearched or duplicated new nodes, no clause moved into a new node, no source tag used as a substitute for a proof citation, no hidden flatness or boundedness hypothesis, and no proof borrowed from a cited node instead of its statement. Each cited statement has a verbatim quote in citations.json. proof_deps is exactly the union of uses. All four steps are below 2000 characters (438, 1063, 516, 569); no long-step sublemma is concealed. The retained statement, definitions and source references have unchanged mathematical meaning.
