# N8 stage-1 report

Item: lem-sfb-rosenlicht-nonproper-affine-subgroup. Statement unchanged. No Lean was written and no compiler, Lake, build, repository git command, or agent was started. All writes are in the assigned sandbox.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-rosenlicht-nonproper-affine-subgroup.json: split into six steps by strong induction on dimension; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-boundary-positive-stabilizer.json: statement, unsplit; no Mathlib match. Gives a proper rational-action model and a positive-dimensional partial stabilizer, without any affineness conclusion.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-fixed-point-affineness.json: statement, unsplit; no Mathlib match. Gives the general local fixed-point criterion, independent of any nonproperness hypothesis.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-subvariety-central.json: statement, unsplit; no Mathlib match. Supplies scheme-theoretic centrality before the existing central almost-complement lemma can be applied.
- citations.json: one verbatim statement quote for each citation in each numbered step.
- searches.jsonl and the saved search outputs: actual msearch.py calls for the item and the three new nodes, including a second semantic phrasing for each. All four services returned normally. No searches were invented. planned-searches.json and second-searches.json list the actual queries; the helper write_split.py is scratch material only.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint tag and id, Rosenlicht, nonproper/noncomplete affine subgroups, rational actions, and fixed-point/centrality terminology. No project declaration states the item or the new inputs. Upstream declarations with sorry would not have counted. Mathlib's Group/Affine.lean is about an already affine group and the Hopf algebra on its global sections, so its Loogle hit does not prove affineness of a general group.

## WANTED

WANTED: J. S. Milne, A Proof of the Barsotti-Chevalley Theorem on Algebraic Groups (2013), arXiv:1311.6060v2, Proposition 4.1 and Lemmas 4.3--4.4, pp.7--9, for lem-sfb-rational-boundary-positive-stabilizer and lem-sfb-rational-fixed-point-affineness. I read those pages online at https://arxiv.org/pdf/1311.6060 and did not download or write the article. The local Milne 2017 book explicitly refers to this article. Since the detailed document is not held in literature/, the item's proof_origin is agent. The local source field remains Milne 2017 with the exact reference and the WANTED notice; the two new nodes carry statements only.

## Issues in the imported material

The item's statement is correct. The source's tempting sketch assumes an equivariant completion, but its footnote explains that Theorem 8.44 establishing such a completion depends on Proposition 8.25. Using that sketch would introduce circularity. I retained the source's rational-action route instead. The original node correctly warned of this issue but had no proof. No statement dispute or change of hypotheses was needed.

The ancestor command returns None, as on the reviewed parent. I retained blueprint.from.node null and the inherited via list, adding this item to the new nodes' via lists and specifying exact places in Proposition 8.25's rational-action proof. I read the current latest blueprint stability unit and its direct-images proof; the inherited route is retained, with no change to the unit or chapter. Whole-DAG and whole-blueprint searches for Rosenlicht, rational/local actions, boundary stabilizers, fixed points, and abelian subvarieties found no matching blueprint node.

## Not duplicates

lem-sfb-rational-boundary-positive-stabilizer vs lem-sfb-smooth-group-orbit-geometry: the latter assumes an affine acting group and a globally regular action. The new input treats the rational extension of translations of a possibly non-affine group, produces a suitable proper model and boundary point, and asserts no affineness.

lem-sfb-rational-fixed-point-affineness vs lem-sfb-general-group-centre-zero-dimension-affine: the latter concerns the centre and conjugation of a group on itself. The new input allows an arbitrary faithful regular action on a dense open variety and a fixed point of its rational extension; it needs no condition on the centre's dimension.

lem-sfb-rational-fixed-point-affineness vs lem-sfb-conjugation-finite-jet-kernel: the latter assumes an affine acting group and identifies the kernel of conjugation jets; it cannot establish affineness for a general group acting near a fixed point.

lem-sfb-abelian-subvariety-central vs lem-sfb-rosenlicht-connected-almost-complement: the existing almost-complement statement assumes that the embedded abelian variety is central; the new result proves that hypothesis for an arbitrary abelian subvariety of a connected group.

lem-sfb-abelian-subvariety-central vs lem-sfb-general-group-centre-zero-dimension-affine: representability and the zero-dimensional-centre criterion do not say that an abelian subvariety lies in the centre.

The three new nodes have no Stacks tag in common with existing nodes. They are neither elementary facts nor clauses of the item's conclusion: the boundary result gives no affine subgroup, the fixed-point result has a separate local-action hypothesis and no subgroup-existence conclusion, and centrality has no nonproperness or affine-subgroup conclusion. The item's induction, reductions and case assembly remain in its own proof.

## Review by N8

I read Milne 2017 Proposition 8.25 and its footnote on printed pp.153--154; Proposition 8.9 on p.150; Corollary 8.13 and Definition 8.15 on p.151; Theorem 8.24 on p.153; and Corollaries 1.35 and 1.39 with the dimension discussion on pp.17--18. For the boundary and rational fixed-point inputs I also read the referenced 2013 article's Definitions 4.2, Lemmas 4.3--4.4 and Proposition 4.1 proof online. The new centrality node follows Corollary 8.13 and its preceding anti-affine discussion, independently of the dichotomy. I checked that all three new statements introduce their objects and explain rational maps, faithfulness, partial stabilizers, normality and affineness where needed. I read the actual statement field of every cited node; citations.json copies these fields verbatim and never quotes a proof or a title instead.

Step 1 uses the dimension clause of lem-sfb-affine-normal-subgroup-products, not its unrelated product clause: it explicitly covers all closed subgroups of a separated finite-type group, and strict smooth connected inclusions. The zero-dimensional-closed-subscheme node applies with X=Z=G and the identity immersion, so no properness is assumed in advance. Finite-proper then contradicts nonproperness. I checked Stacks 06LH, varieties.tex, lemma-algebraic-scheme-dim-0, in the local source. This is a genuine induction base, not an assumption that dimension is positive.

Step 2 takes exactly the proper model, rational map, boundary point, definition domain and positive-dimensional subgroup asserted by the new boundary input. The identity-component node applies to S without assuming S smooth, connected or affine. Its statement gives a closed reduced smooth connected integral component with unchanged underlying topology. The component-translates statement covers nonreduced groups as well and explicitly gives finitely many isomorphic open-and-closed components, from which the dimension equality is a short topological argument. No affine orbit theorem is applied to the non-affine group G.

Step 3 is the case that this smooth connected subgroup equals G. The partial fixed locus is a closed equalizer inside V; since its closure is all of G it is dense in V. I explicitly used smooth-geometrically-reduced to justify that V is reduced before promoting set-theoretic vanishing to vanishing of its ideal. Evaluation at the identity of the dense regular orbit proves scheme-theoretic faithfulness on all algebra points. Thus all hypotheses of the rational fixed-point affineness node hold. Taking U=G uses the already established positive dimension. The criterion does not presume that the rational action is globally regular on X.

Step 4 uses the strict dimension drop with smooth connected C and G. In the nonproper case the strong induction hypothesis applies, and composite closed immersions are justified directly by composite quotient maps. No new node was created for that elementary composition or for substitution in the induction hypothesis.

Step 5 assumes C is proper, in addition to the smoothness and connectedness already proved. This is precisely the definition of abelian variety used here. Centrality is a separate cited result and is not silently inferred from commutativity. I then checked the existing almost-complement statement: it requires a CENTRAL abelian subvariety and returns smoothness, connectedness, separatedness, finite type, closed normal inclusion, faithful flatness, surjectivity and the dimension sum. Those are exactly the properties this step uses; positive dimension of C gives the smaller dimension for N.

Step 6 checks rather than assumes that N is nonproper. Proper base change and composition make C times N proper if N were proper. The proper-image statement applies because G is separated and finite type. Its scheme-theoretic image is all of G, by surjectivity plus reducedness; I wrote the nilradical argument explicitly. This contradicts nonproperness and makes the induction hypothesis applicable to N. Nothing requires N to be affine. Composing the resulting U into G gives every requested clause and does not assert normality of U.

I checked the new statements against Ga and Gm acting on a projective completion (a full stabilizer at the boundary), an abelian variety (nonproperness excludes the boundary input), a product of an abelian variety with Ga (positive-dimensional proper subgroup and almost-complement cases), trivial groups, disconnected stabilizers, and characteristic-p infinitesimal subgroups. In particular I used a reduced identity component rather than assuming a scheme stabilizer is smooth. A proper abelian factor is central without requiring G commutative. The fixed-point criterion excludes trivial actions through its faithfulness hypothesis, including infinitesimal kernels.

I reviewed delivery-errors B--E against all four JSON files: statement-only new nodes with definition dependencies, actual searches, no duplicate or mere restatement, every non-elementary step cited, no proof-only information extracted from a node, induction hypotheses checked, and no equivariant-completion or Chevalley cycle. All six steps are below 2000 characters; there is no long step hiding an uncited comparison lemma. Generic external tools are declared in split_report.tool_uses only; no maintainer-owned tool_uses field was added.

## Unfinished work

No part of this one-level split remains unfinished. The three deliberately unsplit inputs join the stage-1 queue. None is a Mathlib leaf. The detailed 2013 article is requested above for the literature collection.
