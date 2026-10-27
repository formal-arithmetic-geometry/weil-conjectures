## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-presentation-pseudocoherence-invariance.json (item, statement, split; no Mathlib match), citations.json, report.md. No new nodes and no Mathlib leaves.

Attachments: none. Searched lean/WeilConjectures by the exact blueprint tag, pseudo-coherence names and polynomial-presentation terminology, and checked lean/Sheaf for the evaluation ingredient. No completed project declaration states this item. Existing sorry declarations are not treated as proofs.

WANTED: none.

The imported statement is correct, including arbitrary rings and unbounded derived objects. It and its statement dependencies are unchanged. The empty imported proof is replaced by four steps. Nothing remains unfinished in this one-level split. The existing scalar-restriction theorem has the same unit and its dependency closure does not contain the item (32 nodes checked), so this citation introduces no cycle.

## Sources and route

Read literature/stacks-project/more-algebra.tex, Tag 065H (lemma-relatively-pseudo-coherent), Tag 065G (lemma-add-variable-pseudo-coherent), and Tag 064Z (lemma-finite-push-pseudo-coherent). The first is exactly the requested full pseudo-coherence independence; its proof uses a common polynomial ring and repeated variable elimination. The first proof paragraph of 065G uses the existing 064Z theorem. Our evaluation at b is its translated-variable version, with the injectivity and kernel calculation proved explicitly. Read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This remains lower-level algebra for the inherited direct-image chain; no unit route is replaced. The ancestor tool returns None; retained the inherited null ancestor and via chain.

## Searches and reuse

Searched the whole DAG for 065H, 065G, lemma-relatively-pseudo-coherent, lemma-add-variable-pseudo-coherent, polynomial/restriction pseudo-coherence, and variable/zero pseudo-coherence. Blueprint searches for pseudo-coherent, 065G, add variable and polynomial presentation found no equivalent blueprint statement (the polynomial-presentation hit sk-d-geometry concerns affine varieties, not this assertion). Reused lem-sfb-pseudocoherent-algebra-scalar-restriction, whose statement is precisely the general 064Z equivalence. The one-variable lemma is now a two-term resolution followed by that existing theorem, so creating a separate node would violate the elementary/duplicate rule.

Ran and read LeanFinder twice for the item and twice for the evaluation ingredient, LeanSearch for both, Loogle with PseudoCoherent and Polynomial/MvPolynomial, and a whole-Mathlib pseudo-coherence grep through msearch.py. All services answered; grep and Loogle had zero hits. Semantic hits concerned cohomological support, ordinary module finite generation, free/projective resolutions without pseudo-coherence finiteness, and finite algebra presentations. None is an exact or one-line match. searches.jsonl retains the actual responses; item mathlib_searches retains the inherited records and appends every current query verbatim. No unavailable service was called a no-match.

## Review by NS

I read 065H and its proof against every clause of the item: both maps are surjective R-algebra maps, with finitely many variables; they present the same A; K is any object of D(A). No Noetherian, flatness or finite-presentation assumption entered. I read the statements of def-weil-pbc-mv-polynomial-ring, def-pc-ring-pseudo-coherent-complex, and lem-sfb-pseudocoherent-algebra-scalar-restriction, and copied verbatim statement excerpts into citations.json for each use.

Step 1 uses the polynomial definition and bounded-above finite-free definition, not an unquoted resolution theorem. I checked the kernel formula by t^i-b^i, surjectivity by constants, and injectivity by the highest nonzero coefficient. The two-term complex is in degrees -1 and 0 and has its only cohomology B in degree 0. It therefore verifies the actual algebra hypothesis of 064Z. This argument is elementary, including over rings with zero divisors; no regularity theorem is hidden in it.

Step 2 cites the scalar-restriction node's full equivalence, whose hypothesis is that the target ring as a module is pseudo-coherent. Step 1 supplies exactly that for B[t] to B. The citation does not assume flatness or an isomorphism of scalar-extension complexes, and says exactly what is needed for arbitrary L. The node's source 064Z confirms the full pseudo-coherence clause.

Step 3 cites the polynomial universal property, which explicitly gives evaluation and uniqueness. The two surjectivity hypotheses supply the f_j and g_i respectively; their displayed image equations prove equality of the two composite maps on all generators. I checked the two polynomial regroupings by the inverse maps on variables, and the equality of restricted complexes by their scalar actions, so neither an unstated transport lemma nor a derived tensor comparison is used.

Step 4 uses the uniform equivalence already established from the scalar-restriction theorem, with the polynomial universal property at every evaluation. I checked that f_j is in P, hence in every P_{j-1}, and g_i is in Q, hence in every Q_{i-1}; all displayed maps therefore have the stated targets. The induction starts with the original restricted complex, and ends with exactly the same T-complex on both sides by step 3. It does not cite 065H as a black box. The induction claim, base case, successor and terminal identifications are written out.

For edge cases I checked r=0 and s=0 (empty identity inductions), K=0, A=0, and rings B with zero divisors in step 1. For example Z/4 and b=2 still give an injective monic multiplication map. For P=k[x] to k with x acting by zero and Q=k, the two-term resolution gives precisely the expected equivalence. No cohomological boundedness is smuggled into the arbitrary-complex step. All four steps are below 2000 characters. B1-B9 are satisfied without new nodes; C1-C4 are accounted for by the explicit elementary calculation and the opened 064Z statement; D1-D5 are avoided by the actual common-ring assembly and explicit induction. E1-E6 were checked at the maps and hypotheses just described. No statement dispute or source error was found, and no SGA source is used.
