# Stage-1 delivery: lem-sfb-borel-opposite-root-dichotomy

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-borel-opposite-root-dichotomy.json`: item split in five steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-centralizer-borel-intersection.json`: one new statement-only theorem, unsplit; no Mathlib match. It is the general theorem for an arbitrary torus inside a Borel of a smooth connected affine group, with no reductivity or maximal-torus hypothesis.
- `citations.json`: eleven records, one for each node used in each step, containing verbatim excerpts of the cited statements (whole statements where several clauses are used).

## Attachments

None. I searched all of `lean/WeilConjectures/` for the item tag, Borel, reductive, and rootSpace. The only reductive hits were unrelated Lie-algebra representation comments. There is no project declaration giving this group-scheme theorem. The project's sorry declarations were not treated as completed proofs.

## Literature wanted

None. All proofs follow the local `literature/milne-algebraic-groups_iAG2017.pdf`, especially Theorem 17.46, pp.365--366, Lemma 20.20, pp.414--415, and Theorem 21.11 and Lemma 21.28, pp.428--433. No SGA route is used.

## What needed repair

The imported item had no proof. Milne's short proof uses a genuine theorem: the intersection of a Borel with a torus centralizer is a Borel of that centralizer. The DAG did not state it. I extracted that general theorem as the sole new node. The rest is an actual reduction and matrix computation, not a restatement of the opposite-root conclusion in a child node.

The existing rank-one theorem supplies the finite root-space decomposition, opposite roots, one-dimensionality, and reductivity and semisimple rank one of the root centralizer. I reused it and the existing explicit matrix-pair classification. I did not cite `lem-sfb-reductive-borel-pair-structure`, the regular-cocharacter Borel theorem, or the SL2 parametrization node: they lie above this item or depend on results above it and would give a circular route.

I initially considered extracting the assertion that Borels in the three rank-one matrix models stabilize lines. After opening the existing solvable fixed-point theorem, I kept this as a direct application in step 3: fix a point of the proper projective line, include the Borel in its triangular stabilizer, and use Borel maximality. The triangular stabilizer's smoothness, connectedness and solvability are checked explicitly. This is elementary assembly from the cited fixed-point theorem and matrix definitions, so it is not another node.

`tools/blueprint_refs.py ancestor lem-sfb-borel-opposite-root-dichotomy` returns `None`. The pre-existing created.item chain ends with the Lean module `Sheaf.SixFunctors.CtfStabilityDirectImages`, although its textual provenance names `det-thm-sf-ctf-stability-direct-images`. I retained the current item's null from.node and used the same null on its child, with the full place and via chain. I did not edit another node to repair that pre-existing chain. I read the current blueprint under `literature/blueprint/latest/`, including the six-functor stability unit and direct-image proof (3); this is the supporting alteration chain already recorded by the parent, not a change to a unit or chapter route.

## Not duplicates

lem-sfb-torus-centralizer-borel-intersection vs lem-sfb-torus-centralizer-smooth-connected: the existing node gives representability, smoothness and connectedness of a torus centralizer; it does not say its intersection with a Borel is maximal solvable in that centralizer.

lem-sfb-torus-centralizer-borel-intersection vs lem-sfb-maximal-torus-centralizer-borel: the existing node puts the centralizer of a maximal torus inside a Borel; the new node applies to an arbitrary smaller torus and asserts Borel maximality of an intersection in its larger centralizer.

lem-sfb-torus-centralizer-borel-intersection vs lem-sfb-chevalley-borel-intersection: the existing node identifies the reduced identity component of the intersection of all Borels through a maximal torus. The new node concerns one Borel and the centralizer of any torus it contains, with the full scheme intersection.

lem-sfb-torus-centralizer-borel-intersection vs lem-sfb-reductive-torus-fixed-subgroup: the existing node gives reductivity of a torus centralizer in a reductive group; it neither assumes a Borel nor states the intersection theorem. The new theorem permits nonreductive groups.

The searches covered the whole DAG by title/statement and by Milne places 17.46, 17.72, 20.20 and 21.28; only the item and its ancestors used the latter root-dichotomy places. Whole-blueprint searches for Borel, root, centralizer, torus centralizer, Borel centralizer and triangular found no same statement. Projective-line and proper-projective-space searches found the existing properness node, which is reused. There are no Stacks-tag duplicates in the new node; its source is Milne, with exact printed theorem numbers and pages.

## Mathlib searches

All service queries were run through the required msearch.py command, and their actual query text and hits are recorded in searches.jsonl and the applicable nodes. For both the item and the new node I used LeanFinder, LeanSearch, Loogle and grep, with a second natural-language phrasing before the no-match verdict. LeanSearch's root-pairing positivity results presuppose a base and do not prove any relationship with an algebraic Borel. The Lie-algebra root-space results have differential weights and characteristic-zero/Killing hypotheses; I read the Killing source and the root-pairing Base structure to check this mismatch. Centralizer searches returned abstract-group centralizers, whose statements give no group-scheme representability or maximal smooth connected solvable subgroup. All services answered; none was marked unavailable. Searches of the abandoned matrix-Borel candidate are also preserved in the log but produced no new node.

## Review by NZ

I read Milne Lemma 21.28 on printed p.433 and Theorem 21.11(b),(c) on pp.428--429, including the rank-one proof and the use in Proposition 21.29 on p.434. The item is correct without a characteristic restriction because its weights are group-scheme torus characters. I did not change its statement, hypotheses or conclusions.

For the new node I read the full statement and proof of Theorem 17.46 on pp.365--366 and the restatement 17.72 on p.376. The source assumes a smooth connected group variety and a torus contained in a Borel; those are precisely the node's hypotheses over the algebraically closed field. Its intersection is C_B(S), which is smooth and connected by the centralizer results invoked in that proof; Borel maximality is the substantive extra claim, not supplied by the existing centralizer smoothness node. The node introduces the centralizer functor on all algebra extensions and defines the scheme intersection. It contains no proof or proof dependencies.

Step 1 uses the actual statement of `lem-sfb-reductive-rank-one-reflections`: it explicitly gives the finite decomposition with zero weight Lie(T), one-dimensional root spaces and Q-alpha intersection equal to the opposite pair. These are not inferred from a definition. Step 2 uses that same node for the rank-one reductive centralizer and the new node for D being a Borel of H. Here S is contained in T and T in B as required; T is still maximal in H. The new theorem is applied to the original smooth connected G, not to a possibly singular intersection.

Step 3 uses the statement of `lem-sfb-split-rank-one-classification`, which explicitly identifies the pair including its diagonal torus and works in characteristic two. It uses `lemma-nagata-projective-space-base-change-proper` for properness, and `lem-sfb-solvable-proper-fixed-point` for a scheme-theoretically fixed point. The acting group D is smooth connected solvable from step 2. The projective line is nonempty and finite type, and its matrix action is algebraic; central scalar matrices act trivially, so PGL2 acts on it too. A fixed F-point is a line; the diagonal torus forces it to be a coordinate line. The stabilizer calculation uses equations over arbitrary F-algebras. Maximality of D then identifies it with that smooth connected solvable triangular subgroup. Thus no inference from mere containment of point sets to subgroup-scheme factorization is used.

Step 4 uses the classification for the three tangent calculations, the rank-one theorem for the opposite-pair root dimensions and absence of other rational multiples, and character antiduality for the free lattice and primitive-character coordinates. I checked the statement of the antiduality node; it explicitly provides the split group algebra and character equivalence, not merely a named definition. The dual-number computations identify Lie(C_G(S)) with S-fixed tangents and Lie(B times_G H) with the intersection of tangents. They require no smoothness assertion about an arbitrary fibre product: this particular D is already smooth by step 2. The off-diagonal classes in gl2/FI are not killed in characteristic two. No claim is made that d(alpha) and d(-alpha) are different linear functionals.

Step 5 is elementary coefficient comparison in the already supplied weight decomposition. T normalizes B since it lies inside B, so the restricted coaction lands in b tensor the Laurent algebra. Independent monomial coefficients put each component in b. A subspace of a one-dimensional vector space is zero or the whole space, giving the direct sum. The final distinctness argument is in the free integer character lattice, where 2-alpha cannot be zero for a nonzero root, even when the field has characteristic two. The eleven citations.json entries were checked as literal substrings of the opened node statements.

For the B--E checklist I checked the new node's self-contained objects and definitions, exact source, normal TeX encoding, empty proof, genuine no-match searches, absence of existing or blueprint duplicates, and complete citations at every non-elementary use. It is not a clause or a renamed version of the item. No route-changing lemma or definition-only citation is used. The projective-space properness result is Lean-closed, so its off-unit use is an allowed closed tool. The other proof nodes are in the item's existing unit. The longest step has 1422 characters, so none exceeds the 2000-character review threshold.

Small cases: if G=T or T has rank zero, there are no roots and the decomposition gives b=Lie(T), with the opposite-pair condition vacuous. For GL2 the upper triangular B contains the upper off-diagonal space only. For SL2 in characteristic two the two roots are plus/minus 2-chi as integer characters, which remain distinct although their differentials can coincide or vanish. For PGL2 in characteristic two the off-diagonal classes survive in gl2/FI. For the new node, S=1 gives C=G and D=B; central S gives the same; G solvable with B=G gives D=C; and S=T maximal in reductive G gives C=T and D=T. These tests respect all hypotheses and reveal no statement dispute.

## Unfinished work

Only the new centralizer-intersection theorem remains unsplit, as stage 1 requires for new supporting nodes. Its future proof follows Milne 17.46: C intersect B is C_B(S), show CB is closed by transporter closedness and rigidity of homomorphisms from S to the torus quotient B/B_u, identify C/(C intersect B) with its closed orbit in G/B, and deduce Borel maximality from properness. These ingredients are for the future worker to split, not hidden assumptions of the current proof.
