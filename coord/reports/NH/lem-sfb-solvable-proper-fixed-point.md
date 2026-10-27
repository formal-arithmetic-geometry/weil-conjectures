## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-solvable-proper-fixed-point.json: statement, split into five proof steps; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-solvable-homogeneous-proper-subschemes.json: new statement-only node, unsplit; no Mathlib match. This is Milne Theorem 17.1 with explicit scheme quotient data, not the fixed-point theorem.
- citations.json: a verbatim statement quote for every step/node pair.
- searches.jsonl: queries actually run through the authorized msearch command, with its original results and digests.

## Attachments

None for the item or new node. Searching lean/WeilConjectures for the item tag and for solvable/Borel/fixed-point terminology found only unrelated Lie-algebra or finite-action results. The existing generic tool lem-kun-dimension-finite-type already carries the completed declaration AlgebraicGeometry.exists_topologicalKrullDim_le; I read its present source at WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:212--223. No Lean was written or compiled.

## WANTED

None. The actual proof source is locally available as literature/milne-algebraic-groups_iAG2017.pdf. No SGA source is used.

## Corrections and scope

There is no mathematical statement change or statement dispute. The item already has exactly the smooth connected solvable acting group and nonempty proper finite-type scheme required by Milne Corollary 17.3. I normalized the inherited doubled TeX escapes, and checked the written new node and proof for the same escaping problem.

The old item was statement-only. Its source identified Theorem 17.1 and orbit lemma 1.66 but did not give the argument. The new split writes the minimum-dimension choice, the boundary contradiction, the closed orbit's properness, the stabilizer quotient identities, and the application of Theorem 17.1. In particular, it does not replace the stabilizer by its reduction, and it does not infer scheme-theoretic fixedness just from equality on rational points.

The nearest blueprint ancestor command returns None for this inherited long creation chain. I kept that inherited from.node value, placed the exact supporting sentence in the new node's from.place, and prepended the item to the inherited via list. The route anchor remains the latest blueprint direct-images proof (3), which I read together with the current unit and chapter records. This supporting item is not the unit's key node, so it does not change realized fields or the unit/chapter route.

## Not duplicates

lem-sfb-solvable-homogeneous-proper-subschemes vs lem-sfb-solvable-proper-fixed-point: the new node concerns arbitrary homogeneous quotients and all proper closed subschemes inside them, even when the ambient quotient is not proper; the item concerns an arbitrary proper scheme with an action and must first find a closed homogeneous orbit. The minimum-orbit construction is retained in the item's proof.

lem-sfb-solvable-homogeneous-proper-subschemes vs lem-sfb-smooth-group-orbit-geometry: orbit geometry gives local closedness, flatness, smoothness, stabilizers and boundary dimension inequalities for arbitrary smooth connected acting groups. It gives no obstruction to positive-dimensional proper subschemes of a homogeneous space. The new input is specific to solvable groups.

lem-sfb-solvable-homogeneous-proper-subschemes vs lem-sfb-algebraic-group-homogeneous-quotient: the existing node constructs quotients for arbitrary group schemes and closed subgroups. It imposes no solvability and gives no restriction on proper subschemes or proper quotients. I read its statement and reused neither its proof nor hidden constructions.

Before creation I searched the whole DAG by statement text for solvable quotients, complete subschemes, proper homogeneous spaces and orbits; I also searched Milne 17.1/17.2 and the relevant id. The whole imported blueprint was searched with blueprint_refs.py for fixed point, solvable (14 matches, Lie-algebra notions/results), homogeneous (40 matches, projective grading and unrelated notions), orbit (3 matches, unrelated Frobenius/additive topics), complete subscheme (0) and proper homogeneous (0). No node states Theorem 17.1 or a generalization. The existing reductive-borel-pair-structure node depends on this item; I did not cite it back and create a cycle.

## Review by NH

I read Milne iAG2017 Corollaries 17.2--17.3 and Theorem 17.1, printed pp.352--353 (PDF pp.364--365), Proposition 7.4 and the stabilizer definition on pp.139--140, Proposition 7.11 and its proof on pp.141--142, and Definition 5.20/Propositions 5.24--5.25 on pp.104--105. The item is Corollary 17.3 over an algebraically closed field. Properness is Milne's completeness; smoothness and connectedness are hypotheses on the acting group, and no assumption on reduction or connectedness of X is needed. The new node states the independent geometric Theorem 17.1, including its assertion that a complete quotient forces the subgroup to be the whole group. Its right-torsor isomorphism and faithfully flat map spell out the scheme quotient used there. The subgroup is allowed to be nonreduced and disconnected, just as in that theorem. It carries no proof or proof dependencies, introduces all objects, and defines solvability and the quotient data explicitly.

For step 1 I opened the statements of lem-sc-lft-over-field-jacobson-space, lem-weil-pbc-closed-point-residue-field-base, lem-kun-dimension-finite-type and lem-sfb-smooth-group-orbit-geometry. The first really asserts density of points closed in X in every closed subset; applied to X itself this gives a point because X is nonempty. The second gives its residue field as F. The dimension node gives a global finite bound, not merely a finite dimension at each point. The orbit node gives a nonempty locally closed orbit for every rational point. Subspace dimension is bounded by ambient dimension by taking closures of the chains and intersecting back; hence a least nonnegative orbit dimension exists. I checked Stacks Tag 0478 at varieties.tex label lemma-locally-finite-type-Jacobson and the cited residue-field source, Tag 00FV, algebra.tex theorem-nullstellensatz (scheme passage Tag 01TB).

For step 2 the same orbit node actually states invariance of both the orbit closure and boundary and the strict inequality for every boundary orbit, including for nonreduced X and nonreduced stabilizers. The boundary is closed in the closure since the orbit is open there, hence closed in X. Thus the Jacobson statement applies to that boundary, not an arbitrary subset. Its closed point is rational by the same residue-field statement and contradicts the explicitly chosen minimum. No irreducibility or connectedness of X enters this argument.

For step 3 the orbit node supplies the reduced locally closed subscheme and the faithfully flat map onto it, as well as the closed stabilizer with its functor-of-points equation. Closed support turns that immersion into a closed immersion. I opened lem-weil-pbc-proper-fp-permanence: clause (c) says a closed immersion is proper and clause (a) says proper morphisms compose. Applying precisely those clauses makes O proper over F and therefore separated and finite type. No smoothness of the stabilizer is inferred from flatness of the orbit map.

For step 4 I checked the stabilizer equation in the orbit node and the universal property in def-pc-fibre-product. If hx=h'x, then multiplying by h inverse gives (h inverse h')x=x over the same algebra, and conversely. The displayed inverse (h,h') -> (h,h inverse h') uses actual scheme multiplication/inverse maps, with factorization through the stabilizer fibre justified by this equality; it is not only a bijection of F-points. Both composites cancel by the group identities. This is an elementary construction from the cited statements, not an unrecorded orbit-quotient comparison theorem.

For step 5 I compared every hypothesis of the new node with the data from steps 3--4: H is smooth, connected, affine, finite type and solvable by the item; K is its closed scheme stabilizer; O is proper, hence separated and finite type; q is faithfully flat, right K-invariant, and has exactly the required relation isomorphism. The new node says K=H as closed subgroup schemes when the quotient is proper. Combining that conclusion with the quoted stabilizer equation gives the fixed-point identity over every F-algebra, including nonreduced algebras. It gives every clause of the item, without any reduction of X.

I tested the new statement on K=G (quotient a point), G=1, G=G_a or G_m with K=1 (nonproper quotient, only zero-dimensional proper closed subschemes), and G=G_a in characteristic p with K=alpha_p (the Frobenius quotient remains G_a; this verifies why no smoothness assumption on K is allowed). For the item, trivial H, disconnected proper X, and nonreduced proper X all work through the same orbit argument. Translation of G_a on itself shows why properness cannot be omitted; a disconnected group swapping two proper points shows why connectedness of H cannot be omitted. Smoothness is retained as required by Milne Remark 17.5. No characteristic-zero restriction was added.

I read the returned Mathlib hits for both semantic phrasings of the new input and the broader follow-up search: they concern abstract solvable quotients, topological complete group quotients, affine-space integrality and topological torsors, not group-scheme homogeneous spaces. The Loogle query returned 0 hits, the targeted AlgebraicGeometry grep returned 0 hits, and the broad grep returned unrelated homogeneous-localization, manifold and affine-torsor documentation. The exact tools and query texts in mathlib_searches are in searches.jsonl; no unavailable service was counted as a no-match. The item's inherited searches were also actually rerun and read. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the written files: only the substantive geometric input becomes a node, all used non-elementary facts are cited statements, no proof of a dependency is borrowed, no new hypothesis is invented, and no step exceeds 2000 characters. citations.json quotes the complete verbatim statement for each citation, so every quoted assertion can be checked directly.

## Validation

The preliminary authorized server review_split invocation returned PASS. Full delivery dry-run and push results are recorded below when completed.

## What remains

The new statement-only input is deliberately left unsplit for a later stage-1 item. No part of the requested one-level split is deferred.
