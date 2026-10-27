# Stage-1 report: lem-sfb-etale-stack-localization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-stack-localization.json: statement, split; seven explicit proof steps, no Mathlib match. The statement is unchanged.
- citations.json: a verbatim statement excerpt for every dependency of every proof step.
- report.md: this report. Searches are retained in searches.jsonl.

New nodes: 0. Mathlib leaves added: 0. No unit or chapter record changed: this item is a supporting lemma, not its unit's key statement.

## Attachments

None. Searched the live project's lean/WeilConjectures by the exact blueprint tag and by stack/localization and fibred/fibered vocabulary. No declaration states the complete item. The upstream descent extensions deal with morphisms or descent data for a fixed pseudofunctor and do not give this equivalence of 2-categories.

## WANTED

None. The source needed here is available in literature/stacks-project/.

## Corrections and source route

The item was unsplit with no proof. Its mathematical statement is correct, and no hypotheses or conclusions were changed. Stacks 04WT (section-localize), Constructions A and B, explicitly omits the stack checks, and 04WV (lemma-localize-stacks) says only that the inverse constructions are clear. The split supplies those checks rather than citing 04WV as a black box or moving either direction into a new node. Its proof_origin is agent because these omitted arguments have been supplied here.

The inherited blueprint.from.node was null: blueprint_refs.py ancestor also returns None because the creation chain terminates at an intermediate Lean-module name. Its inherited from.place already explicitly names det-thm-sf-ctf-stability-direct-images. I read the current latest blueprint's statement and proof of that node and repaired from.node to that actual blueprint id, retaining the inherited via and place. Paragraph (3) is the proper/open direct-image route; the inherited stable-moduli and algebraic-stack inputs lie beneath its open-direct-image input. No route above the node level is replaced. Whole-DAG searches and blueprint_refs.py searches for 04WV, stacks over, fibred in groupoids and localization found no equivalent blueprint statement, so same_as remains [].

## Mathlib searches

Retained all searches already on the item, and appended only the five searches actually run by Q49 through msearch.py (all are in searches.jsonl). Read the IsStack and descent-data hits in Mathlib/CategoryTheory/Sites/Descent/IsStack.lean and the existing project descent extensions. IsStack and isEquivalence_toDescentData concern a fixed pseudofunctor, not localization of the 2-category of stacks. Read overEquivPresheafCostructuredArrow in CategoryTheory/Comma/Presheaf/Basic.lean:613: it is a set-valued presheaf equivalence, not the groupoid-valued stack statement. The second LeanFinder phrasing returned CoGrothendieck fibre equivalences and general category localizations; these do not assert either stack check or this 2-equivalence. No hit is an exact match or a one-line specialization.

## Not duplicates

No new node was created. In particular, I reused lem-weil-pbc-small-etale-representable-presheaf-sheaf instead of creating a big-etale representable-descent node. Applying that statement on the small etale site of T to the T-scheme T times over S' with S gives exactly the local gluing and local equality needed here, by the universal property in def-pc-fibre-product. There is no restriction on that T-scheme: S to S' need not be etale, finite type, or separated.

## Review by Q49

I read the full localization section in stacks.tex, especially the hypothesis that h_U is a sheaf, both constructions, and 04WV. I also read the representable-sheaf result 03O3 (lemma-representable-sheaf-fpqc) in etale-cohomology.tex and the setoid-stack characterization mentioned immediately before the constructions. The proof does not use the latter characterization as an uncited theorem: step 1 verifies its special case directly. I opened the statement of every cited node: def-sfb-stable-pointed-moduli-groupoids supplies the explicit lifting/unique-factorization definition, functors and natural isomorphisms over the base, and the two etale stack axioms; def-pc-fibre-product supplies existence and the universal property; lem-weil-pbc-small-etale-representable-presheaf-sheaf supplies gluing of maps into any T-scheme over a small-etale cover. There are no new-node sources to review.

Step 1 uses those three statements. For any T over S', T times over S' with S is a T-scheme, and its representable sheaf on T_et evaluates at V/T as Hom over S' from V to S. This checks exactly the base hypothesis in Stacks 04WT and proves the discrete isomorphism-sheaf assertion by local equality; it does not assume big-etale subcanonicity without a cited result.

Step 2 uses the fibred-groupoid definition only. Its lift is over V with structure a composed with u. The structure equations for arrows into x force the intermediate arrow v to commute with S, so the original unique-factorization axiom applies. Applying a base-preserving functor to a cartesian arrow gives a cartesian arrow here because every arrow in a category fibred in groupoids has the stated universal property.

Step 3 uses the same three cited statements as step 1. I checked that isomorphisms are not mistakenly taken just in one fixed F(T,a) when x and y initially have different S-structures: local isomorphisms first force equality of those structures, and the cited representable sheaf gives global equality. Only then is the sheaf condition in F used. No representability of the isomorphism sheaf is assumed.

Step 4 again uses the three statements. Applying p to overlap isomorphisms gives the actual equality of local structure maps; the cited sheaf lemma glues them to a map T to S over S'. The datum, with exactly the same overlap isomorphisms and cocycle, is now on a cover of that S-scheme, so effectivity is part of the hypothesis on F. No descent theorem for schemes or for algebraic stacks is being smuggled into this step.

Step 5 uses just the fibred-groupoid definition. The lift by the original G projection automatically has the prescribed structure map because q is a functor to the slice. The factorization supplied by the original projection is over the desired slice arrow because a slice arrow is uniquely specified by its underlying arrow and endpoints. Thus no general composite-fibration lemma is required.

Step 6 uses the same three statements as step 1. For fixed S-structures, isomorphisms in the original G fibre are already over the identity in the slice. After descending objects in G, the resulting structure b need not initially be declared equal to a: their local equality follows by applying q to the descent identifications, and the cited representable-sheaf uniqueness proves b=a. This is the missing check in Construction B.

Step 7 uses the explicit 1- and 2-morphism conventions in the definition node. Commuting with the displayed map to h_S is exactly being over Sch/S, on functors and on natural-isomorphism components. Both constructions keep the total categories and all these maps, so identity and the two compositions agree literally. Applying both operations returns p, or returns (G,jq,q)=(G,r,q), respectively. Thus this proves the 2-category assertion as well as the object assertion.

I checked delivery-errors B--E against the actual files. The only non-elementary input beyond the stack hypotheses is representable-sheaf descent, and it is cited whenever used; the other steps explicitly check the defining equations. No subclaim has been moved to a new node, no statement-only source tag is used as a theorem, and citations.json quotes the actual statements, not proofs. All seven steps are below 2000 characters. The source has no additional hidden lemma here: both omitted verifications have been written out. There is no reliance on any SGA source.

Small cases checked: g the identity (the two projections are unchanged); S empty (a nonempty T has no S-structure and the empty cover over the empty scheme forces the usual contractible empty fibre); a subterminal F represented by an open subscheme of S (no object is introduced over a T whose structure map does not factor through that open); two different maps T to S (there are no fibre isomorphisms unless they agree, as step 3 requires); bases and morphisms without finiteness or separation; and nontrivial automorphism groups (all total arrows and 2-morphisms are retained). Empty covers are covered by the cited sheaf lemma and the stack descent hypothesis. No smallness of an indexing category beyond the fixed size convention is invoked, and no colimit of groupoids is formed.

The representable-sheaf lemma is a generic tool from another unit. I declared it in split_report.tool_uses, explaining its use on T_et; it does not replace the inherited alteration or direct-image route. No maintainer-owned top-level tool_uses field was written.

## Unfinished work

None in this one-level split. The cited existing representable-sheaf node remains an existing dependency for its own stage-1 work.
