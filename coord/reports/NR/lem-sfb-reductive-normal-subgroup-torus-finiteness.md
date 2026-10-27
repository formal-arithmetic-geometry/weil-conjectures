## Worker report

Item: lem-sfb-reductive-normal-subgroup-torus-finiteness. Group: NR. Stage 1, direct delivery, 2026-10-24.

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-reductive-normal-subgroup-torus-finiteness.json: the unchanged statement with six proof steps; status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-subgroup-maximal-torus-intersection.json: statement-only structural lemma, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-connected-normal-subgroup-reductive.json: statement-only structural lemma, unsplit, no Mathlib match.
- report.md, citations.json and searches.jsonl document this delivery. milne.txt and write_split.py are sandbox research material, not delivery files.

Attachments: none. I searched lean/WeilConjectures for the exact blueprint tag and for reductive, torus, normal subgroup and normalSubgroup. The torus hits concern compactness in trace bounds; the reductive hits concern Lie algebras; the normal-subgroup hits concern abstract representations and Galois groups. None states the group-scheme item or either new structural lemma. In particular, no sorry declaration is counted as a finished proof.

WANTED: none. The Milne PDF and Stacks TeX needed here are present.

The sandbox initially contained only dispatcher brief markers, with no previous split, report or search log. I copied the current item, retaining its source, statement and all six prior search records. The node had no proof and was unsplit. No released repair note exists. The item statement is correct; no STATEMENT-DISPUTED correction was needed. I did not edit the repository, the launcher, Lean files or any unit record, and ran no Lean, Lake or compiler command.

The proof follows the item's stated Milne route through the reduced identity component. The source's finite-intersection hypothesis forces its maximal torus to have rank zero. The existing scheme-theoretic self-centralizer theorem supplies triviality at that point; this is a direct specialization of Milne 17.61(a), without a new rank-zero lemma. The final finiteness assertion is applied to N itself, preserving its nilpotents. The total assembly text is approximately 3,100 characters; no step exceeds 2,000 characters or conceals a further comparison lemma.

## New nodes

lem-sfb-normal-subgroup-maximal-torus-intersection states Milne Corollary 17.85, printed pp.379-380, in the smooth connected affine case over an algebraically closed field. I read both its statement and conjugacy proof. The intersection need not be reduced: the maximal torus is its reduced identity component. I read Notation 12.29 (p.241) and Remark 12.5 (p.232) for this interpretation of the largest subtorus. G and M are not assumed reductive. This is a structural theorem about all normal subgroup varieties and has neither the item's finite-intersection hypothesis nor its finiteness conclusion.

lem-sfb-connected-normal-subgroup-reductive states Milne Corollary 21.53, printed p.441. I read that corollary and the preceding semisimple normal-subgroup corollary. The source's phrase "subgroup variety" is rendered explicitly as a smooth connected closed subgroup. It is not applied to the possibly nonreduced N. The general theorem has no chosen torus and asserts reductivity, not finiteness. The printed proof has Ru(G) where the context calls for Ru(N); the theorem statement is unambiguous and true, and our delivery does not reproduce that typographical inference as a proof.

For each new node I ran msearch.py under this item's NR sandbox: LeanFinder, Loogle, a grep in AlgebraicGeometry, LeanSearch, and a second LeanFinder phrasing. The exact five queries for each node and original result summaries are in its mathlib_searches and searches.jsonl. Loogle and grep returned zero hits; semantic hits were abstract Frattini/normal subgroup facts, topological connected components, Cartan Lie subalgebras or characteristic-zero Lie radical results. They do not state either scheme-theoretic assertion. All services answered. I also searched the item with those four tools and a second semantic phrasing, retaining its older searches.

## Blueprint and existing-node searches

I read SETUP's three levels, the chapter and unit records, and the current latest blueprint files sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The inherited supporting chain serves direct-image clause (3), through the kernel-finiteness step of lem-sfb-torus-simple-root-isomorphism-criterion. I read its uses of this item. Neither the chapter nor the unit route is changed.

blueprint_refs.py ancestor returns None for this existing created-item chain. I retained the item's inherited from.node=null and via list; each new node prefixes this item to that via list and names its exact Milne structural input in from.place. Whole imported-blueprint searches "torus", "maximal torus", "normal subgroup variety", "reductive", "17.85" and "21.53" found no equivalent imported node; "normal subgroup" found only abstract-representation, component-coset and definition nodes. same_as is therefore empty.

Whole-DAG searches of the statements, titles, Milne numbers, "normal subgroup", "reduced identity", "maximal torus" and "reductive" found existing nodes that handle smooth identity reduction, ambient geometric normality, torus self-centralizers, and zero-dimensional finiteness; I cite them. The only existing source-number matches for 17.85/21.53 are the item and its parent criterion. I also opened the nearby subdirect-product reductivity, central-isogeny compatibility, radical quotient, quotient torus-image and multiplicative-type largest-subtorus statements. None gives the two missing inputs. Traversing dependencies of the proposed reused inputs found no path back to the item.

## Not duplicates

lem-sfb-normal-subgroup-maximal-torus-intersection vs lem-sfb-reductive-normal-subgroup-torus-finiteness: the new lemma gives the maximal torus of a smooth normal subgroup in any smooth connected ambient affine group; it assumes no finite intersection and proves no finiteness. Steps 1-6 still carry the item's argument.

lem-sfb-normal-subgroup-maximal-torus-intersection vs lem-sfb-torus-simple-root-isomorphism-criterion: the existing parent concerns a surjective reductive homomorphism and root-group isomorphisms, not maximal tori of arbitrary smooth normal subgroups. It depends on our item, so cannot supply the structural input.

lem-sfb-normal-subgroup-maximal-torus-intersection vs lem-sfb-multiplicative-type-largest-subtorus: the existing node constructs a largest subtorus of a multiplicative-type group; it does not say that intersecting a maximal torus of G with a normal subgroup produces a maximal torus of that subgroup.

lem-sfb-normal-subgroup-maximal-torus-intersection vs lem-sfb-quotient-borel-torus-images: that node concerns images under faithfully flat homomorphisms, not intersections with normal subgroups.

lem-sfb-connected-normal-subgroup-reductive vs lem-sfb-reductive-normal-subgroup-torus-finiteness: the new lemma gives reductivity of every smooth connected normal subgroup, with no maximal torus or finite-intersection hypothesis and no finite conclusion.

lem-sfb-connected-normal-subgroup-reductive vs lem-sfb-subdirect-product-reductivity: the latter requires two surjective projections to reductive factors; a closed normal inclusion into one reductive group is not that setting.

lem-sfb-connected-normal-subgroup-reductive vs lem-sfb-central-isogeny-borel-root-compatibility: that theorem assumes a faithfully flat map with finite central kernel, not a closed normal inclusion.

lem-sfb-connected-normal-subgroup-reductive vs lem-sfb-reductive-radical-quotient: the latter describes the radical and semisimple quotient of an already reductive group; it does not assert reductivity of normal subgroup varieties.

## Review by NR

I reviewed the split myself as required by the direct-delivery brief; no second worker or subagent was started. I read the item source Milne 17.85, 21.53 and 23.24, plus 1.34, 1.38-1.39, 1.52, 1.85-1.87, 17.61(a) and 11.1-11.2. I read Stacks groupoids.tex at Tag 047R (lemma-reduced-subgroup-scheme-perfect) and Tag 0B7R (proposition-connected-component), and varieties.tex Tag 06LH (lemma-algebraic-scheme-dim-0). For each new node the source and interpretation are given above. Both new statements introduce their own field, groups and subgroups, cite definition nodes for every non-inline notion, contain TeX written once, and have empty proof/proof_deps/proof_origin. Neither is an elementary observation nor a clause moved out of the item.

Step 1 uses the actual statement of lem-sfb-locally-algebraic-group-identity-component: it supplies an open and closed subgroup C and a smooth connected finite-type reduction M with the same topology. It is valid for locally finite type, so the finite-type N qualifies. def-weil-pbc-scheme-reduction supplies the closed reduction immersion; lem-weil-pbc-closed-immersion-products supplies composition; the affine-cover criterion makes all these closed subschemes of affine H affine. This avoids silently assuming smoothness of N.

Step 2 uses the reduction definition to check preservation of the nilradical under the conjugation automorphisms. Fixing the identity preserves its connected component by the definition of a connected component; equality of reductions follows on coordinate rings, not merely on F-points. The statement of lem-sfb-smooth-ambient-normality-geometric is exactly the needed upgrade from equality of conjugated subgroup schemes for h in H(F) to normality over every F-algebra. Its essential smooth-ambient hypothesis holds because H is reductive. There is no assertion that reduction is characteristic over arbitrary nonreduced base algebras.

Step 3 applies the new normal-subgroup reductivity theorem only to M, whose four hypotheses were established. It applies the new maximal-torus intersection theorem to H and M: H is smooth connected affine, M is smooth connected closed normal, and the given S is maximal. The new lemma's statement explicitly supplies the closed subgroup R in the intersection and maximality in M. These are exactly what the later steps take from it; no fact is borrowed only from its proof.

Step 4 is elementary coordinate algebra after the cited closed-immersion facts. I opened the base-change node: it allows arbitrary base change of a closed immersion, so it applies to M into N pulled back along N times_H S into N. Composition and the affine-cover criterion give the quotient algebra A onto F[R]. A finite-dimensional quotient stays finite-dimensional by taking the images of a basis. Since R is split, its coordinates are Laurent monomials; for positive rank, distinct nonnegative powers of one variable are independent. The G_m definition gives its Laurent-coordinate model. Thus this calculation proves R=1 inside the item rather than creating an unnecessary finite-torus node.

Step 5 uses the existing self-centralizer statement scheme-theoretically, including arbitrary test algebras. It applies to reductive M and the now trivial maximal torus; F is already algebraically closed, so geometric maximality imposes no extra assumption. C_M(1)=M follows immediately on every test algebra by commuting with 1. Hence M=1 as schemes, not merely that M(F) is a singleton.

Step 6 uses precisely the finite-component and translation clauses of lem-sfb-group-neutral-component-translates, which allow nonreduced and nonsmooth N. The first node's topology clause identifies |C| with the one-point |M|. A finite disjoint union of open singletons has only singleton nonempty irreducible closed subsets, which directly gives topological dimension zero. I read lem-pc-scheme-dimension-local-rings for its equality with scheme dimension. The cited algebraic-dimension-zero node assumes finite type, not properness, so it applies to N. I deliberately did not use lem-pc-dim-zero-finite-over-field, whose statement assumes properness. The finite-morphism definition makes the resulting finite F-module the finite-dimensional coordinate algebra requested by the item.

Small cases checked: H=1 and N=1 give C=M=R=1 throughout; for H=S a torus the hypothesis itself says N finite, and the argument still works; a finite disconnected constant normal subgroup has singleton identity reduction but retains all components in step 6; in characteristic p, mu_p inside a torus has nonreduced coordinate algebra but trivial smooth identity reduction and is correctly concluded finite; the Frobenius kernel of a reductive group is likewise not assumed smooth. For the intersection lemma, G=G_m times SL_2 with M=SL_2 recovers its usual diagonal torus, while M=1 gives rank zero. For the reductivity lemma, M=G and M=1 are included. Dropping smoothness there would incorrectly include Frobenius kernels; that hypothesis is explicit. Positive-dimensional unipotent subgroups of a reductive group are not normal, so they supply no counterexample to either input.

I checked delivery-errors B-E against these files: no new unsplit proof, no hollow data, no duplicate theorem, no full conclusion shifted into a new node, no unsupported non-elementary inference, and no circular dependency. Every step citation has a verbatim statement extract in citations.json. I lengthened extracts where a short conclusion would not display the hypotheses used. No cited step is over 2,000 characters. The statement and all maintainer fields of the item are retained. The reused group-theoretic inputs are in the same inherited unit. I declare lem-pc-scheme-dimension-local-rings and lem-pc-algebraic-dim-zero-affine-finite in split_report.tool_uses as general geometry tools in Step 6: they compare the two dimension conventions and turn the already established zero-dimensional finite-type scheme into a finite scheme. They replace no group-theoretic or unit argument. The other off-unit citations are definitions, Mathlib leaves or Lean-closed statements. No maintainer-owned top-level tool_uses field is written.

## Validation

The first required deliver.py --no-push exited successfully: OK (not pushed), commit 6252866cc7e, server preflight passed (including check_dag and review_split). The final documentation adds the explicit generic dimension-tool explanations and this result; a final dry run is required before pushing. No local DAG checker or preflight was run. The delivery contains two new unsplit nodes and zero Mathlib leaves.
