## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-maximal-torus-centralizer-borel.json: item split in five steps; its statement and statement dependencies are unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-central-maximal-torus-nilpotent.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-normalizer-borel-transitivity.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statement evidence for all four proof citations.

## Attachments

None. Searched the project source under lean/WeilConjectures for the exact blueprint tag, maximal torus, Borel and centralizer. The available centralizer results concern matrix equations or abstract groups, not Borels or the full item. No project declaration gives the item.

## WANTED

None. The actual source, literature/milne-algebraic-groups_iAG2017.pdf, is present and was read. No SGA source is used. This specialized algebraic-group argument has Milne proposition numbers rather than a Stacks-tag source.

## Audit and corrections

The item was an unsplit statement created for the reductive maximal-torus self-centralizer input. There was no previous sandbox split/report/search log to repair. Its existing research and provenance were retained. No statement dispute or correction is needed: the all-algebras containment is valid. A proof using only k-points would leave a gap; the last step instead writes the scalar-extension-compatible conjugation identity for arbitrary A and A-algebras.

Read AGENTS.md, SETUP.md (including the three levels), GOAL.md, the worker role, stage-1 brief and stage, delivery-errors sections B--E in both copies, the relevant tools documentation, chapter/unit records, and the latest blueprint chapter, unit and direct-image proof. The latest blueprint has revised the upper direct-image exposition. This item is a supporting Milne fact below that unit, in the inherited alteration/moduli/PGL route; no chapter/unit route is changed and no unit realization is due from this non-key node. blueprint_refs.py ancestor returns None, matching the existing item's from.node; the new nodes preserve that ancestor and prepend this item to via. Searches of the whole blueprint for centralizer, Borel, maximal torus, central maximal, nilpotent and normalizer found no equivalent blueprint result. Neither new node has a blueprint equivalent, so same_as is [].

The Mathlib searches were run through msearch.py and their actual output read. Each delivered new node and the item have LeanFinder, LeanSearch, Loogle and source-grep records. LeanSearch uses an alternate natural-language phrasing. The semantic results concerned abstract nilpotent/solvable groups, Cartan subalgebras, Sylow normalizer conjugacy and subgroup centralizers. These do not assert the algebraic-group geometry needed here. All services ran; Loogle and the algebraic-group source patterns returned no hits. The full outputs remain in the sandbox and are copied verbatim to the new nodes' results fields. The additional exploratory solvable-subgroup/Borel-extension searches also remain in searches.jsonl; that candidate was not made a node because its argument is the elementary dimension-maximality step below.

## Not duplicates

lem-sfb-central-maximal-torus-nilpotent vs lem-sfb-torus-centralizer-smooth-connected: the existing statement gives smoothness and geometric connectedness of C_G(T), not nilpotence or solvability of a group with a central maximal torus.

lem-sfb-central-maximal-torus-nilpotent vs lem-sfb-reductive-torus-self-centralizer: the existing result assumes reductivity and identifies the centralizer with the torus; the new result concerns arbitrary smooth connected affine groups and nilpotence.

lem-sfb-torus-normalizer-borel-transitivity vs lem-sfb-reductive-borel-pair-structure: the existing result assumes reductivity and supplies a Borel pair/root datum, not conjugacy of any two Borels through a fixed torus in an arbitrary smooth connected group.

lem-sfb-torus-normalizer-borel-transitivity vs lem-sfb-rho-section-modules: the existing statement constructs a Borel pair and rho modules only for semisimple simply connected groups; it does not assert this conjugacy theorem.

Both new nodes vs lem-sfb-maximal-torus-centralizer-borel: neither states the item's containment or a clause of it. One supplies solvability; the other moves an auxiliary Borel to the prescribed one. The item constructs the auxiliary Borel and carries out the centralizer-preserving conjugation argument itself. The existing Chevalley Borel-intersection node is not used: its reduced identity-component equality does not give the required containment for an arbitrary group.

## Review by Q08

I read Milne Corollary 17.39(b), printed p.364, and the immediately preceding Theorem 17.38, printed p.363. The proof of 17.39 cites 17.29 and 12.40. Since the existing torus-centralizer node gives that the full centralizer is smooth and connected, I expand 17.29 directly for that centralizer; no new identity-component containment lemma is introduced. I also read 12.40 on p.244 to check what it does, without treating that normalizer identity as a substitute for connectedness.

For step 1 I opened lem-sfb-torus-centralizer-smooth-connected. Its statement supplies the representing smooth geometrically connected closed subgroup for any torus in a smooth geometrically connected affine group. The algebraically closed base makes its geometric connectedness hypothesis applicable. T is commutative, so its points centralize T after all extensions. Conversely the definition of C makes every point of T central in C. Maximality in G immediately rules out a larger torus inside C. No reductivity is assumed or used.

For step 2 I read Milne Proposition 17.23 on p.359 and Proposition 17.28 on p.360. The new central-maximal-torus node states exactly the nilpotence and solvability being used, with H smooth, connected, affine and finite type. A single central maximal torus suffices: all maximal tori are conjugate and every conjugate of this central torus is itself. That is the (d)/(a)/(b)/(c) implication route in 17.23. Nilpotence is given by a finite central series; its commutator inclusions also force termination of the derived series, so the stated solvability consequence is valid. This node is about algebraic subgroup schemes, not merely their rational-point groups.

For step 3 I initially considered making a Borel-extension lemma, then removed it: dimension maximality is a few-line argument from the already existing dimension assertion. I opened lem-sfb-solvable-normal-subgroup-products and checked that its last sentences explicitly state the strict dimension growth for arbitrary closed inclusions of smooth connected groups, not only for the normal solvable pair used in its first clause. They also give finite nonnegative integer dimensions bounded by dim G. Thus among solvable smooth connected subgroups containing C the maximum dimension is attained; any proper overgroup would have larger dimension. This is exactly maximality in the Borel definition. I read Milne Definition 17.6 and its following paragraph, pp.353--354. This step is elementary relative to its cited dimension statement; no independent extension theorem is hidden there.

For step 4 I read Milne Corollary 17.11, especially its final assertion on p.355, with Theorems 17.9 and 17.10 on pp.354--355. The new normalizer-transitivity statement gives an actual n in G(k), the scheme equality nTn^-1=T, and equality of the two Borel subgroup schemes. Both Borels in this application contain T, which is maximal in G, and G is smooth connected over an algebraically closed field. Its statement includes the all-algebras meaning of conjugation used in the next step. The explicit conjugation formula is a definition, not another unproved comparison theorem.

For step 5 I checked the group identity after every A-algebra extension: if c centralizes T and n normalizes T, then n^-1 c n centralizes T, since c commutes with n t n^-1. This gives n^-1 c n in C(A), hence in B_0(A); conjugating back puts c in B(A). This argument never infers scheme containment merely from a set of geometric points. It proves the requested functor inclusion even for dual numbers and other nonreduced A. There is no extra node citation in this elementary algebra step; the needed conjugacy equality was obtained in step 4.

I checked delivery-errors B--E against the files: both new statements introduce all objects and definitions, cite only definitions used in their text, contain no proof or proof dependencies, and carry actual searches and blueprint provenance. Every non-elementary fact in the item is a cited statement; citations.json quotes precisely those statements. Every proof step is below 2000 characters. Both new statements are true for the trivial group and a torus. For a noncommutative unipotent group with trivial maximal torus, the central-torus criterion correctly gives nilpotence rather than commutativity. The upper triangular group shows why centrality cannot be dropped. In GL_n with the diagonal torus, the normalizer acts on the Borels through T by permuting flags, as required; a connected solvable group has a single Borel and n=1 suffices. Characteristic p introduces no smoothness assumption on an intersection: all groups to which the smoothness lemmas are applied are explicitly smooth. The existing dimension and centralizer nodes are reused, not duplicated. The split changes no statement and introduces no off-unit tool use or circular dependency.

## Unfinished work

Only the proofs of the two new statement-only prerequisites remain for their own future stage-1 workers. That is the required one-level split. No Lean file was written and no compiler, Lake command or build was run.
