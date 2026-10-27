# Q09 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-simple-root-generation-mixed-commutation.json`: statement, split into eight proof steps; no project or Mathlib declaration proves the complete group-scheme statement.
- No new nodes. The live DAG acquired `lem-sfb-root-base-reflection-induction` and `lem-sfb-root-base-rational-integral-spans` during this work. I removed my uncommitted induction leaf and cite the existing nodes instead.
- `citations.json`: 21 verbatim statement excerpts, one for each step/node citation. `searches.jsonl` retains the actual searches and their results.

## Attachments

None. Searches of `lean/WeilConjectures/` by the blueprint tag and by root subgroup, simple-root, normalizer and induction terminology found no declaration giving all clauses. General reflection or Lie-algebra declarations do not prove this group-scheme item.

## WANTED

None. Milne's Algebraic Groups is available locally.

## Corrections and scope

The item statement and its statement dependencies are unchanged. The split supplies the argument, rather than moving its clauses into new nodes. It uses the current blueprint at `literature/blueprint/latest/`, specifically the direct-image proof (3) under `sec-six-functors-basics/sk-thm-sf-ctf-stability/`. This is the recorded alteration/moduli/invariant-theory/root-datum support route; no unit or chapter is changed. The inherited null blueprint ancestor is retained, as required by the read-only metadata rule; the exact inherited place remains present.

The normalizer representatives are constructed inside the candidate subgroup by a three-factor matrix word. The final tangent argument uses all root subgroups, avoiding the invalid general-characteristic shortcut of obtaining all roots from brackets of simple root spaces. Mixed commutation is proved as a polynomial identity on schemes and therefore includes nonreduced test algebras. The candidate closed subgroup need not be smooth or connected.

## Source error

Milne 21.21, printed p.432, says for arbitrary roots that the commutator is trivial if their sum is not a root. Taken literally this includes opposite roots and is false: in SL2, the upper and lower matrices x_+(1), x_-(1) have products [[2,1],[1,1]] and [[1,1],[1,2]], which are unequal in every characteristic, although alpha+(-alpha)=0 is not a root. Its general claim that the commutator subgroup has just the weight alpha+beta must not be used as a replacement for a full root-commutator formula either. This delivery uses neither broad assertion. The item's distinct-simple-root mixed-sign case is true; steps 7--8 prove exactly that case from the independently available ordered-root coordinates of 21.68. Thus the item itself is not statement-disputed and requires no correction. The source's rank-one classification is used through the existing corrected, rank-one pair statement, not the unqualified wording of printed 20.33.

## Mathlib and duplicate checks

I ran the required search command using LeanFinder, Loogle, grep and LeanSearch; all four services returned results. For the item, the hits were abstract Weyl groups, Lie-algebra constructions and unrelated Borel sigma algebras, not reductive-group-scheme generation and commutation. I read the relevant Mathlib source and repeated the search with root induction phrasing. This found `RootPairing.Base.induction_reflect` at `Mathlib/LinearAlgebra/RootSystem/Base.lean:665--674`, with the ordinary-base constructor `RootPairing.Base.mk'` at `BaseExists.lean:311--320`. The constructor's field, spanning and crystallographic hypotheses, and the induction's negation/support/reflection premises were read in context. The initial orbit-span hit in `Irreducible.lean:228` concerns a span under irreducibility and is not the needed conclusion. A malformed final Loogle constructor query returned an unknown-identifier message; I do not treat that result as absence of a declaration.

Whole-DAG keyword and declaration searches and `tools/blueprint_refs.py search` for roots, simple roots, commutators, reflection induction and root induction were read. The existing real-root simple-reflection generation and chamber transitivity nodes do not state predicate induction; the live Mathlib induction leaf does. The existing rational/integral-span leaf supplies the coroot part of a Mathlib Base. All existing supporting nodes were reused. No new node therefore needs a same-tag nonduplication pair.

## Not duplicates

No new nodes remain. The proposed `lem-sfb-root-base-reflection-induction` was discarded when the same existing id and declaration appeared in the live DAG; its content is used by citation. No renamed duplicate was introduced.

## Review by Q09

I read the item source in Milne: 21.41 p.436; 21.62 p.443; 21.23 and 21.21 p.432; 23.21 p.491. I also read 21.2 p.424, 21.11 pp.428--430, the rank-one matrix classification 20.32--20.34 pp.418--419, 21.68--21.69 pp.445--446, and C.11/C.29--C.30 pp.610,614. There are no new-node sources to certify after removing the duplicate leaf. I read every cited DAG statement, not just its proof or title, and generated the citation excerpts from those statements.

1. The Borel-pair statement provides the perfect integral lattice pairing, reduced root datum and sign-coherent simple base. The regular-cocharacter statement really gives a Borel for any regular cocharacter and describes its positive weights. Extending the functional which is 1 on the prescribed base and clearing denominators gives exactly the cocharacter needed; the empty-base conclusion is explicitly included in the cited regular-cocharacter node.
2. The rank-one node supplies finite Weyl action, coroot normalization, and rational reducedness. The lattice-embedding node explicitly restricts the roots to their rational span and states that the restricted coroots span its dual. I verified all its hypotheses with these supplied facts. The rational/integral-span Mathlib leaf supplies both simple-coroot independence and the missing coroot sign property. These are the hypotheses of the actual Mathlib Base required by the existing reflection-induction leaf; no unstated equivalence of base conventions is used.
3. The rank-one node gives G_alpha of semisimple rank one with torus T, exactly the hypothesis of the classification node. That node states pair isomorphisms to the three displayed matrix models. In each, the two offdiagonal additive groups have the prescribed root tangent spaces; root-subgroup uniqueness identifies them. The written matrix product normalizes the diagonal torus, lies in the subgroup generated by those two root groups, and is its nontrivial Weyl class, including in characteristic two. Thus the cited rank-one uniqueness gives the required simple reflection. This is a short matrix calculation from the cited statements, not a separate unproved normalizer lemma.
4. The root-parametrization node states uniqueness as a smooth connected T-normalized subgroup with the exact tangent root space. The displayed conjugation computation gives that root space after a normalizer conjugation, so it gives equality of subgroup schemes, not mere equality of rational points. An element of K(F) conjugates K into itself after every algebra extension. The two-sided predicate on roots is therefore preserved by simple reflections and by negation.
5. The existing induction leaf has exactly these three predicate premises. I checked them individually against step 4 and the generators assumed in K. This applies to a reducible rational root system and does not assume semisimplicity of G.
6. The rank-one node states the full tangent decomposition with the zero-weight summand Lie(T); the root-parametrization node states Lie(U_gamma)=g_gamma. The tangent-generation node explicitly allows arbitrary closed K and a finite smooth connected generating family. Here the family is T plus the finitely many root groups, and every inclusion has already been shown to factor through K.
7. The sign cone is nonempty because alpha and beta are distinct independent simple roots. The finite-hyperplane choice is ordinary rational linear algebra and the denominator argument again uses the perfect lattice pairing. The regular-cocharacter node supplies the new Borel. The coordinate node explicitly states inclusion of each positive root group in its unipotent radical and the T-equivariant product isomorphism in any order. The parametrization node supplies the character action on every test algebra; these are the exact inputs needed for the coordinate polynomials.
8. Vanishing on both coordinate axes eliminates every monomial with a zero exponent. Comparing coefficients of the displayed universal T-equivariance identity then forces the character i alpha-j beta. The same-sign base clause of the Borel-pair statement excludes this for positive i,j. The Laurent-monomial comparison uses characters, not their differentials, so it loses no information in characteristic p. The coordinate isomorphism identifies all-zero coordinates with the group unit. This proves the scheme-morphism statement, not only commutation on F-points.

I checked empty roots (a torus, including the trivial group), rank one (the mixed clause is vacuous), a product of A1 systems, and the adjacent simple roots in SL3, where the mixed root matrices visibly commute. The higher-rank proof excludes mixed coefficients without using good-characteristic assumptions; rank-one representatives also work in characteristic two. Reducibility and central torus directions are retained. The induction leaf's empty-index case is vacuous and its paired-spanning assumptions are met on V and V-dual. Every non-elementary input is cited, and the only elementary steps are the uniqueness/conjugation computation and the two-variable polynomial calculation. All steps are shorter than 2000 characters; none conceals a separate non-elementary comparison. The union of cited nodes equals proof_deps, and a read-only dependency traversal found no path from a cited node back to the item.

## Unfinished work

None for the authorized stage-1 split. No Lean was written and no compiler, Lake, local checker or build command was run. The server review_split check passed with zero new nodes; final dry run and push follow this report.
