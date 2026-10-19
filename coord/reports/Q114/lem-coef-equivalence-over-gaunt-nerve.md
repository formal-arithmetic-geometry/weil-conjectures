# Worker report

## Files written

- dag/nodes/sec-six-functors/lem-coef-equivalence-over-gaunt-nerve.json: statement, split into six explicit elementary steps; not a Mathlib leaf.
- citations.json: a verbatim statement quotation for the sole cited definition at each of the six steps.
- No new DAG nodes and no Mathlib leaves.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint id, gaunt terminology, natural equivalence and functor-equivalence names found no project declaration stating this item. Ordinary derived-category equivalence declarations do not concern these simplicial maps.

## WANTED

WANTED: archived Lurie, Higher Topos Theory, section 1.2.7, for lem-coef-equivalence-over-gaunt-nerve. The online PDF https://www.math.ias.edu/~lurie/papers/HTT.pdf was opened and section 1.2.7, Notation 1.2.7.2, printed p. 39, was read. It provides the functor-object terminology; it is not claimed to state this agent-formulated strict-base lemma. No literature was downloaded or written. The current and older blueprint source directories are not present in this machine's literature tree; the chapter, unit and ancestor DAG records were read instead. The proof is marked agent-written.

## What needed checking

The statement is true without fibrations, and is unchanged. The original node had no argument. Objectwise equality alone would not suffice: a gaunt category need not be thin, and may have noninvertible endomorphisms. Steps 2-4 therefore prove equality on all edges, including mixed product edges, before using the consecutive-arrow description of nerve simplices. The inverse natural transformations and their actual inverse-triangle witnesses are also proved to lie over the constant base; this is needed for the final relative-functor assertion.

The inherited Mathlib records were retained and read. Five Q114 searches are appended exactly from searches.jsonl: LeanFinder in two phrasings, Loogle, Mathlib grep and LeanSearch. LeanSearch was available for Q114; the inherited Q33 unavailable record remains historical. The returned ordinary equivalence declaration and nerve reconstruction/extensionality formulas were inspected at the source lines recorded in the node. None proves the item or supplies it as a one-line specialization. In particular, ext_of_isThin cannot be used for arbitrary gaunt B. Whole-blueprint searches for nerve, identity isomorphisms and natural equivalence found no duplicate; the exchange-identity-pasting hit concerns ordinary derived sheaf base-change maps. Whole-DAG searches also found the parent monoidal-Yoneda citation and other uses of gaunt operator bases, rather than a preexisting theorem replacing this item. The nearest blueprint ancestor was confirmed with blueprint_refs.py ancestor. No new node was created.

## Unfinished work

None in this split. The six steps use only the existing definition and explicit simplicial formulas, and introduce no deferred theorem. Server dry-run and delivery results are recorded below when completed.

## Review by Q114

I read the complete statement of def-cbc-enhanced-diagrams-cones, especially the two-inverse-triangle equivalence convention, the nerve as functors from finite ordinals, degreewise products, and the internal-hom operators. I also read the item's parent monoidal-Yoneda step applying it to N(Delta^op), the six-functors chapter and biduality unit records, and the integral-exceptional-adjoint ancestor. This is a foundational argument below the unit route; it changes neither the unit nor chapter. No SGA source is used. The only outside source consulted was HTT online as specified above; there is no new node needing a separate source.

Step 1 uses the definition's inverse triangles, not a theorem asserting pointwise detection: restricting the inverse and both triangles to a vertex and postcomposing preserves their faces, so the image arrow has a literal two-sided inverse in B. The gaunt hypothesis then makes it an identity, with equal endpoints. This is the easy direction of component detection and has been written out rather than citing the converse theorem.

Step 2 uses the same definition's description of nerves. I checked both product triangles: their shared diagonal is the lower horizontal edge followed by the right identity, and also the left identity followed by the upper horizontal edge. This proves equality of pG and q on arrows, not just objects. Every product edge has weakly increasing parameter coordinates, so it is horizontal or of this mixed form; the vertical case is degenerate in Y. The chain description proves equality of every higher simplex. Step 3 performs the same calculation for the unit after the now-proved pG=q. These are elementary definition calculations, not hidden lifting lemmas.

Step 4 checks the stronger data needed downstream: inverse transformations project identically by the same square argument. In an inverse triangle all three parameter edges have already been shown constant. Restricting to each parameter edge and each domain edge again computes every mixed edge, and the nerve chain gives equality in all dimensions. No assumption that B is a poset, no horn extension, and no fibration has entered.

Step 5 uses the internal-hom formula to specify the actual strict fiber simplicial sets; the hypothesis on n-simplices is p u = a pr_K, not just equality on vertices. It then checks F and G preserve this equality by composition. Step 6 gives the variable-simplex formula for the induced transformations and their inverse triangles. Restriction commutes with this formula, all base composites remain a pr_K by steps 3-4, and the original face equations remain the inverse-triangle equations. The conclusion uses exactly the assumed quasicategory property of the two relative simplicial sets, and does not infer that property from a non-fibration.

I checked empty B (then X,Y are empty), empty K (both relative functor sets are points), terminal B, a discrete B with several objects, B=[1], and the one-object monoid category of nonnegative integers under addition. The last example is gaunt with many noninvertible loops, and confirms why edge equality must be proved rather than inferred from vertices. If the gaunt condition were dropped, B the one-object category of the abelian group C_2, X=Y=N(B), F=G=id and p=q=id, with the nontrivial central group element defining the unit natural automorphism of id (and the identity counit), shows precisely why the projection argument could fail; the assumption is used and retained. Every cited statement was opened and citations.json quotes it verbatim. No statement dispute or correction arose. There are no new nodes, no same-tag pairs, no relabelled clauses and no non-elementary step over 2000 characters; the longest step is under 1400 characters. The only proof dependency is the existing definition, so no cycle can be introduced via a theorem dependency.

## Not duplicates

No new nodes; no pairs to distinguish.
