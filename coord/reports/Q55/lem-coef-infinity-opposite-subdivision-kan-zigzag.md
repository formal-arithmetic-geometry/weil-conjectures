## Worker report

Files written:

- dag/nodes/sec-six-functors/lem-coef-infinity-opposite-subdivision-kan-zigzag.json: statement, split into nine steps; no exact Mathlib match.
- citations.json: fourteen verbatim statement quotations, covering every step/node pair.
- report.md: this report. searches.jsonl records the five Mathlib searches actually run in this sandbox. No new nodes and no Mathlib leaves.

The sandbox initially contained only the dispatch markers. There was no earlier split, report, search log or delivery result to overwrite. The interrupted provider call had performed reads only. I read the current shared item and continued the originally dispatched item. The statement, stmt_deps, original source, created ancestry and blueprint fields are unchanged. Only the split fields and additional actual searches changed. No Lean was written or compiled and no git command was run by me.

## Attachments

None. Searches of WeilConjectures/ in the read-only slopmaster2 source by the exact blueprint id and by subdivision, barycentric, opposite simplicial, opFunctor, opEquivalence, ExInfinity and ExInfty found no project declaration of this theorem. The opEquivalence hits concern unrelated ordinary categories or integers. The exact upstream master was also searched by id and the specific notions; no exact declaration was found. No sorry declaration was treated as a proof.

## WANTED

WANTED: archival Kerodon Proposition 3.3.4.8, Tag 00YZ, and Construction 3.3.4.3, Tag 00YU, for the last-vertex input of lem-coef-infinity-opposite-subdivision-kan-zigzag.

WANTED: archival Kerodon Subsection 3.3.6, Tag 00ZA, particularly Propositions 3.3.6.4, 3.3.6.7, 3.3.6.9 and Corollary 3.3.6.8, for the Ex-infinity input and the natural-unit square of this item.

I read these online without downloading into the shared repository. They are Kerodon tags, not Stacks tags. No Stacks tag states this simplicial opposite/subdivision theorem. The flag, quotient and interval arguments are written explicitly by the worker, so proof_origin.by is agent. The blueprint ancestor's derived-adjunction paragraph is the route served, not a claim that the blueprint itself proves the simplicial assertions.

## Findings and completion

No statement dispute or source error was found. The unsplit item already distinguished its last-vertex literature input from the agent-specified reversal assertions; I preserved that distinction. The subdivision functor is not assumed to preserve products. Step 6 exposes the otherwise implicit fact that E preserves weak equivalences: naturality of j and model-category two-out-of-three, using the existing Kan-Quillen model-structure node. All proof dependencies already exist. Nothing remains mathematically unfinished in this one-level split.

The chapter and unit records and the three blueprint levels were read. I did not change their statements or route. This item is technical support for paragraph 2 of prop-coef-integral-exceptional-adjoint through the retained opposite-duality step 7 of lem-coef-infinity-relative-cone-equivalence. All theorem dependencies are in the item's unit; the enhanced-diagrams node is a definition and introduces no off-unit proof route.

## Searches and not duplicates

Whole-DAG and whole-blueprint searches for opposite, subdivision, barycentric, last-vertex, Ex-infinity and path reversal found the existing face-poset calculus, last-vertex equivalence and Ex-infinity theorem that are now cited, and the parent relative-cone node that uses this item. The blueprint_refs ancestor command returned prop-coef-integral-exceptional-adjoint; searches for subdivision and Ex infinity found no blueprint node and the broader opposite search only unrelated opposite categories/correspondences. No new node is proposed, so there is no new/existing duplicate pair to justify.

Five actual msearch.py queries were read: two LeanFinder phrasings, LeanSearch, Loogle SSet.opEquivalence, and grep in AlgebraicTopology/SimplicialSet. All services returned hits. The first semantic query returns the categorical opposite involution; the second returns finite edge-path/spine operations. Neither states a clause about the realization, subdivision zigzag or the path-object pullback. I opened the pinned Mathlib Op.lean and Subdivision.lean: Op.lean lines 21-26 explicitly leave horn reversal and realization identification as TODO; lines 42-107 implement only the opposite involution and its categorical equivalence. Subdivision.lean lines 39-56 construct sd, ex and their adjunction, with no Ex-infinity theorem. The existing searches inherited with the item are retained; the five appended records are exactly this sandbox's successful logged queries, not invented replacements. No Mathlib leaf can discharge this full item in one line.

## Not duplicates

No new nodes.

## Review by Q55

I read the item, its entire statement and every cited node's statement, with Kerodon 00YZ, 00YU and 00ZA open. In 00YZ the last-vertex assertion is for an arbitrary simplicial set, which is crucial because Sd(T) need not be Kan. In 00ZA the unit, Kan output and finite-limit assertions are distinct; the item uses all three without asserting that subdivision preserves products. The definition node gives precisely the quotient topology, coordinate-sum realization relation, all-horn Kan condition, degreewise products/pullbacks and the internal functor formula used here. There are no new-node sources to review.

Step 1 uses def-cbc-enhanced-diagrams-cones for standard simplices and horns. I checked conjugation of monotone maps, composition and involutivity, and that the omitted vertex i goes to n-i, including outer horns. These are explicit computations, not a cited theorem about opposites.

Step 2 uses lem-coef-subdivision-face-poset-calculus for the degreewise colimit by subset images and the enhanced-diagrams definition for nerves. Its statement actually supplies this presentation, so I do not use its proof. I checked the relation with a simplex t of every dimension: the arrow alpha in T becomes bar-alpha in T-op, and rho alpha(S) = bar-alpha(rho S). Inclusion order of flag terms stays unchanged; reversing that order would be wrong. Deletion and repetition of flag terms prove simpliciality directly. Double reversal and relabelling of t give the inverse and naturality. No colimit-existence theorem for a large category is used: the category of simplices of a small simplicial set is small and the cited node already defines this specific colimit.

Step 3 uses the exact final sentence of lem-coef-subdivision-last-vertex-equivalence at T and T-op, the natural lambda clause of the face-poset node and the definition of weak equivalence. I checked that eta has a strict simplicial inverse, hence a continuous realized inverse; its weak-equivalence property needs no separate hidden homotopy theorem.

Step 4 uses only the explicit realization quotient in def-cbc-enhanced-diagrams-cones. I checked R_n |alpha| = |bar-alpha| R_m coordinate by coordinate, then used the quotient topology to descend the continuous representative map. Both composites are identities. This proves a homeomorphism, not just a bijection of realizations.

Step 5 uses the weak-equivalence and Kan definitions of that same node. Naturality of the homeomorphism identifies the induced component and based-group maps. For horn filling, I checked the direction Lambda_i -> T-op becomes Lambda_(n-i) -> T, and that the reversed filler restricts to the original map. No nonemptiness assumption is inserted.

Step 6 uses the statement of lem-coef-ex-infinity-finite-products for every-A Kan output and the natural weak-equivalence unit. It also cites lem-coef-kan-quillen-model-right-proper-core, whose assertion of a model structure provides its two-out-of-three axiom. The equation (Ef)j_A = j_B f first shows the composite weak, then cancels j_A. I did not silently infer weak-equivalence preservation from finite limits or from the definition of Ex.

Step 7 uses that same model-structure node for composition and the Ex-infinity statement for Kan objects, units and finite-product comparison. The inputs to E are weak equivalences already proved in Step 3. Only the two end objects require the hypothesis that T is Kan; Step 5 supplies it for T-op. I checked all four naturality squares and then specialized those squares to each product projection, using the coordinatewise opposite definition. The empty product is included by the terminal comparison of the existing Ex node.

Step 8 uses the enhanced-diagrams internal-functor and degreewise-product definitions. I checked its explicit formula at a general m-simplex (beta,gamma), its compatibility with a source operator alpha, and separately its compatibility with a parameter operator a. The latter has to use bar-a on the source opposite functor space. The endpoint 0 goes to 1 and vice versa. The formula squares to the identity, with no choices of path inverses in a Kan complex. This avoids the false assertion that Delta^1 has a simplicial self-map exchanging its vertices.

Step 9 uses the same degreewise pullback and functor definitions and the already constructed Step-8 formula. I checked each of the two endpoint equations and the inverse triple map. On a constant path, h(beta,gamma)=W(gamma)w; after reversal its value is W(bar-gamma)w, exactly the constant path at w regarded in W-op. Thus compatibility with strictly commuting squares is proved on every simplex, not asserted just on vertices. Naturality is coordinatewise postcomposition.

Small cases checked: empty T (empty subdivision, empty realization and vacuous horns), T=Delta^0 (all reversals identities), T=Delta^1 (subset reversal exchanges singleton vertices and fixes the full subset), discrete Kan T (constant paths), n=1 outer horns, empty and singleton product families, and empty U or V in the path pullback. For the non-Kan Delta^1 I checked only the clauses quantified over arbitrary T. I also enumerated all monotone maps with source and target dimensions at most 3, checking 5,374 composable-map reversal identities and every nonempty subset-image reversal identity. This is a finite consistency check, not a substitute for the general displayed calculations.

Against delivery-errors B–E: there are no new nodes, hollow data, duplicate subclaims or renamed item clauses. Every non-elementary input is an existing theorem node, every used notion has its definition, and all fourteen citations are verbatim substrings read from those statements. The proof union is exactly proof_deps. No step exceeds 2,000 characters (maximum 1,240), and each explicit reversal calculation stays with the corresponding requested construction. No target hypothesis, coefficient category or base-change morphism was changed, no chapter/unit was edited, and no prohibited source was used. The local self-check initially looked for the enhanced-diagrams definition in the item's chapter; I corrected the lookup to search all chapter directories. That was only a local checking-script path error; the cited id is the existing definition in sec-smooth-purity.
