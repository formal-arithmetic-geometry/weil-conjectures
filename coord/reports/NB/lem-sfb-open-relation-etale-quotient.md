# Stage-1 delivery: lem-sfb-open-relation-etale-quotient

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-open-relation-etale-quotient.json: statement, split into seven steps; not a Mathlib leaf.
- citations.json: 27 verbatim cited-statement entries, covering every uses entry in every step.
- report.md: this report. No new nodes; zero new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by open relation, quotient etale, quotient_stack and quotientStack terminology. No project declaration states all the clauses. Sorry declarations are not treated as finished proofs.

## Wanted literature

None. All sources used are in literature/stacks-project/. No SGA source is used.

## Corrections and scope

The mathematical statement is unchanged. Its imported TeX had literal doubled backslashes before arrows; these were normalized to single TeX commands. The imported empty proof was replaced by the argument of Stacks 0DU1, lemma-quotient-etale. There is no STATEMENT-DISPUTED claim: the statement is correct, including when U is empty or U -> Y is not surjective.

I read the chapter and unit records, SETUP's three levels, and the current latest blueprint direct-images proof, paragraph (3). Its current route is proper/open direct images and compactification. The inherited long alteration-chain blueprint place is historical provenance and was preserved; this split supplies the local quotient prerequisite, without changing a chapter or unit route. blueprint_refs.py ancestor returns None, matching the inherited null ancestor. The existing via list is retained. Whole-blueprint searches for quotient, open equivalence relation and quotient-etale found no blueprint statement identifying this item with another node. same_as remains [].

## Mathlib searches

The sandbox searches.jsonl records two genuinely executed LeanFinder phrasings, one LeanSearch query, one Loogle query and a source grep. Both semantic phrasings were read. Returned AlgebraicGeometry.IsEtale/Etale and Scheme.Etale describe scheme morphisms; DiscreteQuotient.mk describes topological setoids, not algebraic spaces; CategoryTheory.Pseudofunctor.IsStack and its locality predicates supply neither algebraicity nor this quotient theorem. I read Mathlib/AlgebraicGeometry/Morphisms/Etale.lean (definition Etale, lines 40 onward) and Mathlib/Topology/DiscreteQuotient.lean (structure at line 75) to check the domains. The source grep's sole hit was a comment on OpenPartialHomeomorph equivalence relations. Loogle for AlgebraicSpace and Etale had zero hits. No match was inferred from an unavailable search; all five sandbox searches returned successfully. Earlier search records inherited from the live node are retained unchanged, with the five current searches appended.

## Not duplicates

No new nodes were created. Reused the existing flat-groupoid, algebraic-setoid, fppf-descent and chart-calculus nodes. In particular, did not create a second node for Stacks 04SZ, 06FI, 06FH, 04XD or 05W1, or a node for the elementary product-cover factorization or the sheaf gluing argument. A whole-DAG search for 0DU1/lemma-quotient-etale and relevant phrases was read: no distinct node states the entire item. The similarly named unramified-space-open-diagonal is the forward direction with scheme target; the cited space-unramified-open-diagonal is exactly the reverse direction used here.

## Review by NB

I read Stacks stacks-morphisms.tex Tag 0DU1 in full, including the phrase "small detail omitted"; criteria.tex Tags 06FH and 06FI; algebraic.tex Tag 04SZ; stacks.tex Tag 02ZP; stacks-properties.tex Tag 04XD; and spaces-morphisms.tex lemma-diagonal-unramified-morphism and lemma-unramified-flat-lfp-etale. There are no new-node sources to audit. I read the statement of every cited node, and citations.json quotes each such statement verbatim, while the following specifies the clause actually used.

Step 1 uses open-immersion-etale only after scheme base change. def-trf-algebraic-space then gives representable etaleness. The stack-chartwise-smooth-etale-calculus statement explicitly supplies base change, composition and etale -> smooth -> flat and lfp. Therefore the projections of U x_Y U, and then s,t, have the hypotheses of the groupoid theorem. This does not assume U -> Y surjective.

Step 2 uses the complete statement of flat-groupoid-algebraic-quotient: algebraicity, the representable surjective flat lfp presentation and the arrow/self-fibre-product equivalence. Its groupoid laws and base are exactly those of the item; no field, smoothness or Noetherian hypothesis is added.

Step 3 uses this same equivalence for automorphisms of represented objects, the scheme open-immersion definition for uniqueness of lifts, and stackification-local-description for local representatives and sheaf isomorphisms. Local identity automorphisms glue uniquely even on nonreduced test schemes. This verifies the all-test-schemes hypothesis of algebraic-setoid-space, rather than substituting the weaker geometric-inertia condition of the DM lemma. The extension property in the stackification node supplies the structure map to Y.

Step 4 uses sheafification only by the universal property its definition actually states, never by an unquoted plus-construction or an unsupported assertion about local representatives of sheafification. Local representatives come from the stackification node. The relation equivalence in the flat-groupoid node gives agreement on overlaps. Since A and X are fppf sheaves (for X this is explicitly in def-trf-algebraic-space), the images glue, and refinements prove independence and naturality. The inverse equations follow by local equality for X and universal-property uniqueness for A. This is an elementary assembly of the cited interfaces, not a new quotient lemma.

Step 5 uses exactly the source-local flat/lfp clause of representable-fppf-etale-open-descent, with V=Y and W=U. Identity covers are justified by the isomorphism clause of space-representable-etale-scheme-tests and the smooth-etale calculus. This avoids incorrectly descending etaleness along a source cover, which the cited node explicitly does not assert.

Step 6 uses the base-change and composition clauses of stack-chartwise-smooth-etale-calculus for the two maps of the product presentation. The first is the base change of p along the first projection X x_Y U -> X; the second is its base change along the second projection X x_Y X -> X. Thus q really has all three covering hypotheses. The flat-groupoid node identifies R with U x_X U, and fibre-products-etale-covers supplies the algebraic-space fibre products. The cartesian pullback of the relative diagonal is computed on sections. Only then is the target-local open-immersion clause of representable-fppf-etale-open-descent applied. This supplies the detail omitted in 0DU1, rather than introducing a node restating the item's conclusion.

Step 7 uses the calculus's lfp -> lft implication before applying space-unramified-open-diagonal, whose lft hypothesis is essential. Common etale scheme charts exist by the algebraic-space definition and the fibre-product node. The representable scheme-tests node ensures their composite source chart is surjective etale. The local-properties-chart-test gives flatness and lfp for this actual chart pair; unramified-etale-compatible-charts gives unramifiedness of that same h. The scheme etale definition is precisely the conjunction of these three properties. The compatible-chart node then gives etaleness of f. No additional algebraic-space flat-unramified theorem is silently used.

I checked delivery-errors B--E point by point against these files: no unsplit new-node proof sketches, missing new notions, fake searches, relabelled conclusion nodes, use of another node's proof, hidden source-local etaleness, or unstated finiteness assumptions. The longest step has 985 characters, so none reaches the long-step threshold. Off-unit citations are generic foundational tools and are declared in split_report.tool_uses, not in a top-level tool_uses field.

Small cases checked: U=R=empty gives the empty etale quotient over any Y; U=Y and the identity relation gives Y; U=A^1_Y with R=U x_Y U gives Y and demonstrates why U -> X need not be etale; for U an open subspace of Y with the diagonal relation the quotient is that open, demonstrating that U -> Y need not be surjective. All arguments allow nonreduced test schemes, non-quasi-compact spaces and an empty target (which forces U empty). No cycle or new dependency on a descendant is intended; the required server dry run checks the entire overlaid DAG.

## Unfinished work

None in this one-level split. Existing supporting nodes retain their own independent stages. Server validation and direct push are performed with the mandated delivery tool.
