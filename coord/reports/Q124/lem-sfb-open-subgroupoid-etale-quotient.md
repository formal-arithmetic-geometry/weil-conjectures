## Worker report

Files written, all under dag/nodes/sec-six-functors-basics/:

- lem-sfb-open-subgroupoid-etale-quotient.json: item, split in six steps; statement and statement dependencies unchanged; not a Mathlib leaf.
- lem-sfb-faithful-stack-map-representable.json: new statement-only node, Stacks 04Y5; no Mathlib match.
- lem-sfb-quotient-map-cartesian-action-groupoid.json: new statement-only node, Stacks 04Y4; no Mathlib match.
- lem-sfb-open-relation-etale-quotient.json: new statement-only node, Stacks 0DU1; no Mathlib match.

Attachments: none. Searches for the exact blueprint tag, subgroupoid, quotientStack/quotient_stack and quotient-stack terminology in lean/WeilConjectures found no project declaration stating this item. Nothing from Mathlib is offered as a project attachment.

WANTED: none. All sources are present in literature/stacks-project/.

The item was an unsplit, statement-only support node created by the reviewed pointed DM neighbourhood split, with no repair note. Its statement agrees with Stacks 0DU2 and adds the valid DM atlas consequence. I found no statement error. Its blueprint ancestor is already null; I preserved that and the inherited via chain, giving the new nodes precise source locations within the inherited support chain rather than inventing an upstream blueprint id.

Nothing remains unfinished in this one-level split. The three new inputs are intentionally unsplit, with empty proof and proof_deps, to enter the next stage-1 queue. No Lean files, compilers, Lake, repository writes or repository git commands were used.

## Searches and blueprint route

Read GOAL.md, SETUP.md's three levels, the fixed chapter and unit records, and the current latest blueprint at main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345. The current local blueprint source is sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This is a general stack-theoretic supporting theorem on the inherited finite-inertia/stable-curve route, not a change of the unit or chapter's six-functor proof. The item is not the unit key node, so no realized fields were changed.

Ran tools/blueprint_refs.py search for subgroupoid, flat groupoid, faithful morphism, quotient stack, quotient etale, representable by algebraic spaces, faithful and cartesian square, and searched the whole DAG by tags 0DU1, 0DU2, 04Y4, 04Y5, 06FI, 06FH and by the corresponding statement terms. No blueprint node states the three new inputs. Existing flat-groupoid algebraicity, stackification, etaleness descent and chartwise calculus are reused. In particular I did not duplicate the already general flat-groupoid quotient node with the affine or smooth special cases.

Every new node was searched through the mandated msearch.py command using LeanFinder (two phrasings), LeanSearch, Loogle and source grep. The item searches were also rerun with their recorded query texts and current results. The first faithful search was read directly and its actual hit names are preserved; all later full results are saved beside searches.jsonl in the sandbox. mathlib_searches records the actual tool, literal query and actual hits. All services answered. Ordinary relatively representable morphisms of categories, scheme pullbacks and scheme etaleness, ring quotient results and topological discrete quotients do not assert the stack or algebraic-space statements here. No match is a one-line specialization, so there are zero Mathlib leaves.

## Not duplicates

lem-sfb-faithful-stack-map-representable vs lem-sfb-self-relation-quotient-embedding: the existing 04Y5-using node only proves representability for the fully faithful quotient of a specific self-relation. It does not state the general fibrewise-faithfulness criterion; the open-subgroupoid map is generally faithful without being full.

lem-sfb-faithful-stack-map-representable vs lem-sfb-finite-type-point-residual-substack: the existing node constructs a residual substack at a finite-type point. Its proof mentions 04Y5, but its statement gives no general faithful-map criterion and has a completely different conclusion.

lem-sfb-open-relation-etale-quotient vs lem-trf-etale-quotient-affine-open-cover: the existing node assumes an etale scheme relation and describes affine-open covers of its sheaf quotient. The new node allows algebraic spaces with only a flat lfp object map to Y, and deduces etaleness of the quotient over Y from openness of the relative relation. The projections of this relation need not be etale.

lem-sfb-open-relation-etale-quotient vs lem-a1-space-invariant-open-quotient: the existing node begins with an algebraic space and its etale atlas and describes invariant opens. It does not construct a quotient or prove etaleness over an arbitrary algebraic-space base.

The general 04Y4 node has no existing node with its source tag or its general morphism-of-groupoids pullback statement. It includes arbitrary object maps and nonfaithful arrow maps; it is not a clause of the item. Likewise 04Y5 is a representability criterion for arbitrary algebraic stacks, and 0DU1 is an algebraic-space equivalence-relation theorem, not the open wide subgroupoid assertion 0DU2. The item's proof carries the passage from the subgroupoid to these inputs.

## Review by Q124

I read Stacks stacks-morphisms.tex Tag 0DU2 (lemma-quasi-splitting-etale), both proof paragraphs, and the entire preceding Tag 0DU1 (lemma-quotient-etale). I also read algebraic.tex Tag 04Y5 (lemma-characterize-representable-by-algebraic-spaces), its full proof; spaces-groupoids.tex Tag 04Y4 (lemma-cartesian-square-of-morphism), its preceding formulas and its full proof; criteria.tex 06FI and 06FH, including their proofs; and the statement/atlas direction of stacks-morphisms.tex 06N3. These are the item's and each new node's sources, and none uses SGA.

Step 1 uses the existing open-immersion-etale statement on scheme charts and the full chartwise-calculus statement for composition and etale => smooth => flat lfp. I read lem-sfb-flat-groupoid-algebraic-quotient: unlike the smooth-groupoid and affine-action nodes, it really covers arbitrary algebraic spaces over any scheme, and explicitly supplies algebraicity and the flat lfp surjective object map. Its hypotheses hold for R and for the restrictions to P. The stackification node really includes the universal extension of functors needed to define j; I read that statement rather than assuming its title covered functoriality. Open-immersion-etale is declared as a generic off-unit tool in split_report, not written into maintainer-owned tool_uses.

Step 2 uses the stackification node's two precise clauses: local essential image and sheafification of Isom presheaves. The algebraic-space definition says they are fppf sheaves, so their representable arrow fibres already give the Isom sheaves. Equality of arrows is local and P is a subfunctor of R. This proves injectivity, not surjectivity on arrows; I therefore did not misuse the existing fully faithful self-relation-embedding node. The new 04Y5 statement gives exactly the general faithful => representable conclusion used here, with both source and target already algebraic by step 1.

Step 3 only uses the field-extension-lifting clause explicitly present in the flat-groupoid node. A field lift to V is also an object of [V/P]; thus j is surjective without any finiteness, separateness, normality of P, or algebraic closedness of the original field. This short argument is marked elementary and cites the statement furnishing the lift.

Step 4 uses the new 04Y4 statement with f_0 the identity, source arrows P and target arrows R. I checked all source/target conventions against the preceding source formulas: R is the object space, B=P times_{s,V,t} R is the arrow space, the invariant base map is s, and (p,r) sends r to c(p,r). The displayed inverse (r_1,r_2) -> (c(r_1,i(r_2)),r_2) has the required source and target. The two cancellation identities prove that the relation is the inverse image of P under the division map, hence an open immersion. This is a routine explicit groupoid calculation; I kept it in the item rather than creating an elementary extra node. Now 0DU1 has precisely the hypotheses U=R flat lfp over Y=V and open relation B -> R times_V R, so it gives etaleness of the actual pulled-back quotient. The new 0DU1 node is statement-only: its source proof, involving flat descent and the open diagonal, was not hidden inside its statement.

Step 5 cites the existing descent node after reading its exact statement. It allows a flat lfp surjective cover by an algebraic space, not just a smooth atlas or a scheme, and its etale assertion is target-local. Thus it applies to V -> [V/R] even when V is only an algebraic space. I have not asserted false source-locality of etaleness.

Step 6 uses the DM definition's actual etale scheme atlas and the algebraic-space definition's scheme chart. With j representable, B=A times_X Y is an algebraic space; chartwise calculus supplies base-change stability, composition and surjectivity to obtain C -> Y. The diagonal was already supplied by the general quotient theorem, so the definition really proves the final DM clause. No theorem about fibre products of stacks already assumed DM is being used to prove DM for Y.

I tested the new statements and the assembly on the empty object space, P=R (identity quotient map), and a groupoid with one object BH -> BG coming from a proper open subgroup H of a flat lfp group G. The last illustrates why j need not be full or a monomorphism, and why no normal subgroup hypothesis is allowed. For 0DU1, the full pair relation on A^1 over a field gives a point quotient, although the projections are not etale; the diagonal relation on A^1 is not open in its relative square and therefore cannot falsely imply A^1 is etale over the field. For 04Y4 I checked the identity groupoid map and a nonfaithful map of one-object groupoids: the action presentation retains stabilizers rather than incorrectly taking a set quotient. All object and arrow sets, covers and the final chart coproduct choices stay within the inherited universes; no smallness or finite-type condition was silently introduced.

I checked B--E of delivery-errors.md: the new nodes are self-contained TeX statements only, their definition dependencies name the notions actually used, source labels and tags match the local .tex, searched terms and negative verdicts are logged, and no lemma is a relabelled clause or an elementary two-line fact. The item's six steps are all under 2000 characters. citations.json contains one literal statement extract for every cited node of every step; I opened every such statement, and the discussion above explains the exact part taken. No source correction, statement dispute, hidden lemma in a long step, or cycle is intended. The server dry run below is the final mechanical verification.
