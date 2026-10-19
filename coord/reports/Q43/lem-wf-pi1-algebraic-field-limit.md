## Worker report

Files written:
- `dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-pi1-algebraic-field-limit.json`: item, statement, now split; statement and statement dependencies unchanged. Ten proof steps, no step above 2000 characters.
- `citations.json`: verbatim statement excerpts for every cited node in every proof step.
- `searches.jsonl`: six searches actually performed with the prescribed msearch command; inherited searches in the item were retained.

New nodes: none. New Mathlib leaves: none.

Attachments: none. The blueprint-id and concept searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no project declaration giving the asserted topological isomorphism for an arbitrary separable algebraic extension and arbitrary separated finite-type base scheme. I read `FundamentalGroup/HomotopyExactSequence.lean`: its constant-cover constructions concern an algebraic closure over a finite field and its results establish portions of the homotopy exact sequence, rather than this full statement. They are not an attachment.

WANTED: none. All used sources were available locally.

What was missing: the item had no proof. Stacks 0BTV (`pione.tex`, label `lemma-limit`, lines 3427–3451) states the result for qcqs inverse systems and calls the fundamental-group consequence formal. I expanded that argument, reusing `lem-wf-finite-etale-field-limit-descent` instead of making a new general limit lemma or restating the item as another node. That existing lemma already supplies descent for objects, morphisms and equalities under exactly the item's field and scheme hypotheses. Only its first two clauses are needed here. No statement dispute or correction was necessary.

No unfinished work in this split. Its dependencies retain their existing stage-1 states; this delivery does not claim new Lean proofs.

## Searches and blueprint

I searched the whole DAG by tag `0BTV`, finite-etale descent terminology and fundamental-group limit terminology, and ran `tools/blueprint_refs.py search` for `fundamental.*limit`, `finite étale`, `fundamental group`, `automorphism`, and `0BTV`. The direct descent node was found and read in full. Other hits for pointed Galois torsors have additional data or restrict the type of cover, and were not substituted for arbitrary finite-etale object and morphism descent. The ancestor command returns `def-wf-fundamental-representation`. I read its current main-20261015 file, the chapter record, the `sk-d-geometry` unit record, and the three levels in SETUP. The unit is an affine-geometry definition with no proof steps. This technical lemma serves the existing arithmetic-lift path construction attached to the ancestor's inverse-image definition of the Weil group, lift choice and usual stalk transport sentence; no chapter or unit route was edited. No blueprint node states the same limit assertion, so `same_as` stays empty.

All six fresh Mathlib searches ran successfully; their exact queries and returned names are in the item and the command's log. The two semantic phrasings found `InfiniteGalois.profiniteGalGrpIsoLimit`, `autEmbedding`, `autEmbedding_range`, `autIsoFibers`, and related declarations. I read Mathlib `FieldTheory/Galois/Profinite.lean:105–140,314–342`, `CategoryTheory/Galois/Topology.lean:35–120`, and `CategoryTheory/Galois/Prorepresentability.lean:280–325,380–425`. The field Galois theorem computes Gal(K/k) from finite Galois subextensions and does not concern fundamental groups of arbitrary schemes. The categorical Galois-object limit concerns one category and its pointed Galois objects, not a directed system of cover categories. The embedding/range lemmas express naturality and the evaluation topology, already represented in the existing definitions, but do not state the item. Grep of Mathlib/AlgebraicGeometry returned no finite-etale/fundamentalGroup declaration. Thus the item is not an exact or one-line Mathlib leaf.

## Not duplicates

No new nodes were created. In particular the existing `lem-wf-finite-etale-field-limit-descent` is cited, not duplicated. The same-tag hits include the parent arithmetic-lift path, finite-etale Weil transport, and pointed Galois-torsor descent; none is a second copy of the item's complete limit isomorphism.

## Review by Q43

I read Stacks 0BTV, `pione.tex`, label `lemma-limit`, including its first assertion and proof, and compared the item's field specialization with it. The item assumes connectedness of every finite stage and of the limit, and fixes one geometric point whose composites supply all basepoints; these are sufficient and are preserved verbatim. The proof uses the already specialized field-limit descent statement, so it does not independently invoke a qcqs-limit theorem without checking its hypotheses. I also read the proof and statement of that descent node, which establishes the qcqs stages, affine transitions and the specified limiting cone before applying finite-presentation descent. The current source of `def-wf-fundamental-representation` was read for ancestry; the actual mathematical source for this item remains 0BTV. There are no new nodes whose sources or statements need separate approval.

Step 1 uses the actual filtered-colimit statement of `lem-kun-algebraic-separable-smooth`; its blueprint proof explicitly uses finite intermediate subfields and their composita. The separable algebraic hypothesis is present, and the indexing collection is a set. The statement of `lem-wf-finite-etale-field-limit-descent` has the same K, L, X0 hypotheses, so object and morphism descent apply to arbitrary finite etale covers here.

Step 2 uses `thm-galois-lc-etale` exactly for its fibre-compatible equivalence, and `def-galois-fibre-functor` for Aut and its evaluation topology. I read both statements; fully faithfulness alone would not suffice. The small-skeleton issue is handled by fixed conjugations of evaluation coordinates and essential surjectivity, so no product over an unspecified proper class is needed.

Step 3 uses the statement of `lem-galois-pi1-functoriality`, which gives the continuous homomorphism, the natural fibre bijection, and its action equation. Both source and target schemes are connected by the item. Composition is checked directly on geometric points using the stated first projections, then on all fibre actions. Product and subspace continuity are the definitions of the topology specified in the item.

Step 4 uses descent clause (1) and the same action equation, then naturality for the descended object's isomorphism. Equality of all evaluation coordinates is equality of natural automorphisms, as stated in the fibre-functor definition. This proves injectivity for arbitrary covers, not just covers descended to the base K.

Step 5 again uses only object descent and the natural fibre bijections to give an explicit conjugation formula. Step 6 checks enlargement by substituting the compatibility equation for a and the functoriality action equation; it is an elementary calculation from those statements, not an extra descent theorem.

Step 7 uses morphism descent clause (2), at a common finite field, for beta inverse composed with alpha. I checked that its domain and codomain are precisely pullbacks of finite etale covers at that field. Naturality of the stage automorphism then proves the displayed conjugation identity. The descended map need not be an isomorphism of schemes; its fibre map is the required bijection because its pullback equals the comparison. This avoids assuming isomorphism descent or using a lemma's proof in place of its statement.

Step 8 applies the same morphism clause to any map P to Q, not just isomorphisms, and writes the naturality equation explicitly. A family of bijective components satisfying that equation is a natural automorphism by definition. Step 9 computes the two inverse identities using exactly the action characterization of functoriality, and reuses the established injectivity; no surjectivity of transition homomorphisms is asserted or needed.

Step 10 fixes one model for each evaluation coordinate. Its evaluation is explicitly a product coordinate, followed by stage evaluation, followed by fixed conjugation between finite discrete permutation groups. The topology statement in `def-galois-fibre-functor` gives continuity in both directions. There is no unsupported appeal to compactness, closed images, or a topological inverse function theorem.

I checked B–E individually: no new unsplit node with a proof, no undefined new objects, no prose tags substituted for cited nodes, no duplicate, no false Mathlib leaf, no transported statement without a formula, no whole clause moved to a new node. Every cited statement was opened and checked; `citations.json` uses exact excerpts. The off-unit inputs are declared only in `split_report.tool_uses`: finite-subfield filtering, specialized finite-etale descent, and the fibre-compatible cover/sheaf equivalence are generic tools absent from this definition unit. The maintainer-owned `tool_uses` field was not changed.

Small cases checked: L=K makes the inverse limit a single stage and both maps the identity; finite L/K gives a greatest field index and the inverse limit recovers that group's coordinate; nonnormal separable algebraic L/K still has common finite subfields and requires no Galois automorphisms of L; the empty cover has its unique empty-fibre permutation and all formulas remain valid; X_L empty is excluded by the chosen geometric point. Arbitrary disconnected finite covers cause no issue because the fibre-functor argument never assumes covers connected. The geometric point need not have its field equal to L; all fibre bijections use its actual fixed algebraically closed field. All ten steps are below 2000 characters and contain only the displayed construction and calculations; no standard comparison lemma is hidden in a long step.
