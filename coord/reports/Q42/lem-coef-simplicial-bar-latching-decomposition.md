# Worker report: lem-coef-simplicial-bar-latching-decomposition

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-bar-latching-decomposition.json`: statement unchanged, split into eight steps. No new nodes and no new Mathlib leaves.
- `citations.json`: a verbatim statement quote for every step/node citation.
- `searches.jsonl`: six searches run with the prescribed msearch.py; earlier searches in the existing node are retained.

The split reuses `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`, an existing Mathlib leaf, and the existing definitions of simplicial set and categorical colimit. The sandbox also contains `write_split.py`, a reproducible local editing script, which is not a delivery node.

## Attachments

None. Searching the entire read-only `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, latching/Latching, simplicialBar and simplicial replacement gave no matching declaration. The master reference is not treated as a completed proof. This item has no inherited Lean declaration.

## WANTED

WANTED: archived copy of Daniel Dugger, *A Primer on Homotopy Colimits*, Section 3.4, Remark 4.4 and Remark 9.12, for this item. I read the [online PDF](https://pages.uoregon.edu/ddugger/hocolim.pdf), specifically printed pp.10, 17 and 38. No copy was found in literature/. Dugger gives the identity-chain description for spaces; the arbitrary-category version is an agent-written universal-property argument using the archived Stacks source, not a claim that Dugger states the present generality. No SGA source is used.

## What was wrong and what changed

There is no statement dispute. The imported statement is correct, including its exact proper-surjection direction, final-arrow convention, degree-zero case, and lack of monicity assumptions. It previously had no proof. I supplied the proof without adding hypotheses or changing its statement dependencies.

The essential existing tool is the unique nondegenerate simplex decomposition. A chain has a unique expression as a degeneracy of a nondegenerate chain, and each surjection preserves the first vertex. A cocone therefore descends to one morphism out of the corresponding label object per degenerate chain. Step 5 writes the comparison for an arbitrary, possibly already degenerate, lower chain; it does not simply assume overlap compatibility.

The first repository lookup did not list this very recent node; it became visible during the shared snapshot refresh. I copied the current existing file, preserving its origin and blueprint ancestry. I read the chapter record, the item's unit `sk-prop-sf-biduality-general`, the NG parent report, and the historical ancestor's current-main-20261015 proof. This is a combinatorial tool below the parent's bar construction; no unit route or geometric duality argument is replaced. No unit record is changed.

## Not duplicates

No new nodes are proposed. Whole-blueprint searches for `latching` and `nondegenerate` and the DAG search found no blueprint node stating this arbitrary-category labelled latching formula. The existing `lem-coef-simplicial-latching-degenerate-subset` states a set-valued latching formula; it does not identify arbitrary-category labelled coproducts. Rather than create a weighted version of that statement as another node, this item's steps give the weighted universal-property argument directly. The existing Mathlib leaf for unique nondegenerate decompositions supplies the genuinely non-elementary fact. Its statement was read in full.

## What remains unfinished

Nothing within this one-level split. There are no new unsplit nodes. The proof depends on the existing three nodes, of which the nondegenerate decomposition and both definitions are Mathlib leaves. Formal Lean work is outside the authorized stage.

## Review by Q42

I read Stacks `literature/stacks-project/simplicial.tex`, `lemma-splitting-simplicial-sets` (Tag 017R, verified in `tags/tags`) and its proof and adjacent splitting definition, and `literature/stacks-project/categories.tex`, `definition-colimit` (Tag 002F, also verified in the tag map). These are the archived sources of the proof. I also checked Dugger's online description of the identity-chain summands and the forward-chain convention; those provide context, while the actual argument and its generalization are explicitly marked agent-written. There are no new-node sources to review.

Step 1 uses the statement of `def-weil-pbc-simplicial-set` for the finite ordinal category and simplicial operators. I wrote out operators on strings, including their final composite to j. Associativity proves their functor equations, so no theorem about an unspecified nerve is being borrowed. The string sets are small since both objects and morphisms of I form small sets. For every surjection its first value is 0, ensuring equality of source objects for label morphisms. This applies only to surjections; arbitrary faces need not preserve the first vertex, and the proof never claims they do.

Step 2 uses that definition's exact degeneracy condition, including arbitrary maps to a smaller ordinal. Such a monotone map has equal adjacent values, hence an identity arrow. Conversely deleting an identity internal arrow provides the required explicit degeneracy. Thus the identification with identity chains is a few-line consequence of the operators, not an uncited theorem about nerves. In particular the final arrow is not tested.

Step 3 applies `lem-weil-pbc-simplicial-set-nondegenerate-decomposition` to the small simplicial set just constructed. Its statement gives precisely existence and uniqueness of the entire triple (dimension, surjection, nondegenerate simplex), not merely existence or a chosen splitting. This is an existing Mathlib leaf, so using it requires no off-unit tool declaration. Its only hypothesis is being a simplicial set. The strict dimension bound for a degenerate simplex follows because a monotone surjection of an ordinal to itself is the identity.

Step 4 constructs the proposed coproduct cocone. `def-weil-pbc-category-colimit` states exactly the cocone equation used. The direction is checked explicitly: theta = rho theta' means an arrow theta to theta', whose diagram map goes from degree a to degree a'. Applying the contravariant chain operators gives T(theta')T(rho) = T(theta). Every structural map is the identity on its label object, since all indexing maps here are surjections. All required coproducts are small and exist by the item's hypothesis.

Step 5 cites both the full normal-form theorem and the cocone definition. I checked them against the factorization equation, including the case where y already has degeneracies. Writing y = T(rho)z gives tau = rho theta and the actual arrow tau to theta. Its cocone equation gives exactly c_tau e_z = c_theta S(rho)e_z. The two domain objects are equal because rho and theta preserve the first vertex. This is an equality of morphisms in M, not an argument with elements of objects of M or with images. No extra colimits or existence theorem is assumed.

Step 6 uses only the colimit definition after the constructions above. Every coproduct injection b_x is hit as k_tau e_z for its proper normal form; this proves uniqueness by testing on injections, without assuming those injections monic. The map to S_n has the stated component e_x, which identifies the canonical latching map. I checked both directions of the uniqueness-up-to-unique-isomorphism comparison against the cited definition.

Step 7 partitions the indexing set and writes the maps in both directions on injections. Testing composites on injections proves the coproduct isomorphism in any category. This is directly the coproduct universal property, not a distributivity theorem or an appeal to disjointness of categorical subobjects. The cited colimit definition applies also to the empty diagram; degree zero is exactly the empty coproduct, hence initial. No summand projection or zero morphism is needed.

Step 8 writes the naturality operations explicitly. Postcomposition changes only the final arrow and hence preserves both internal-arrow subsets, even if some final arrows become identities. A natural transformation of V changes only its label map. Checking the cocone equations on injections and invoking the cited colimit uniqueness proves compatibility of the latching identification; checking the same injections proves compatibility of the binary decomposition. The proof does not require a general map of simplicial sets to preserve nondegenerate simplices.

I tested the statement on n = 0; n = 1 (only the degeneracy of a vertex contributes); the terminal category in degrees 1 and 2 (the two degree-two degeneracy presentations glue to one copy, not two); discrete categories (all positive-degree chains are degenerate); empty I (the claim for j is vacuous); a nonidentity endomorphism; and a category with mutually inverse nonidentity arrows. In the last case the chain of the two nonidentity arrows is nondegenerate even though its middle face is an identity; the proof only tests displayed internal arrows and does not assume nondegeneracy is preserved by faces. A final identity arrow with all internal arrows nonidentity is still in N_n. All these agree with the formulas and hypotheses.

I reviewed delivery-errors B–E against the node and sources. No elementary fact became a new node, no clause was moved into another node, no duplicate was created, no source tag is used as a substitute for a dependency, and no statement was silently weakened. Every cited statement was opened and supplies the part used; citations.json copies those statements verbatim. Both non-elementary steps explicitly cite the normal-form theorem. The remaining steps are written universal-property and chain-operator calculations. Every step is shorter than 900 characters, so there is no non-elementary step over 2000 characters hiding an additional lemma.

For Mathlib I ran two semantic phrasings, Loogle, LeanSearch, and two source greps through msearch.py and read their hits. I read `Mathlib/AlgebraicTopology/SimplicialObject/Split.lean` lines 189–234: the splitting class already assumes its cofan colimit, and `Splitting.isColimit` merely returns that supplied proof. It does not prove the proper-surjection latching formula. The Dold–Kan hits require a preadditive category and a chain complex, absent here. Hence the item is not a one-line Mathlib specialization; the existing nondegenerate set decomposition remains the appropriate leaf. All six new records reproduce actual queries and logged outcomes. Existing records in the item are retained as historical searches.

## Interrupted-turn continuation

The existing split and all logged searches were retained. I compared the current repository item: it remains unsplit, its statement, unit and blueprint ancestry agree with the sandbox, and there is no blueprint update on this item. I re-read the three cited statements and the Stacks splitting and colimit sources. The resumed attachment search in WeilConjectures again found no declaration for the item. The first resumed dry run passed at bd19cad4a4. I checked the decoded proof strings for delivery-errors B4: they contain single TeX backslashes, as required; extra escaping in the tool output is serialization only. The statement and proof are unchanged. I clarified one report sentence: the general colimit definition applies to the empty diagram, rather than explicitly mentioning it. All non-elementary steps remain under 2000 characters. The final dry run and push follow this report clarification.
