## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-vector-trace-geometric-descent.json`: item, split into seven steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-ordinary-affine-counit-tensor-normalization.json`: one new statement-only lemma; no Mathlib match. It identifies the coefficient counit of the explicit ordinary-etale coordinate adjunction, for arbitrary finite A and Noetherian base, with the inverse projection followed by tensoring its unit trace.
- `citations.json`: one literal statement quotation for each step/node citation.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id, vector integration and vector trace notions, and affineTrace tensor/projection formulas. The actual item has no completed project declaration. The proved open-counit tensor identity in `SixFunctors/Etale/Derived/ClosedSupportHom.lean:153` handles only the open factor, not the ordered affine-space counit. It is not an attachment for either delivered statement.

## Wanted

None. This split follows the locally available current blueprint. Its new coefficient-normalization lemma is an agent-extracted statement of a comparison implicit in that route; its proof is deliberately left for the next worker.

## Faults corrected and scope

The item was statement-only. No statement dispute or change was necessary. Its arbitrary finite coefficient ring and arbitrary Noetherian base are broader than the existing pro-etale finite-field coefficient normalizations: applying those would drop hypotheses checks. I retained the actual proper/open exchange, compositor and coefficient-first projection. I did not use smooth purity to establish the trace identities, nor any SGA source. In particular the parent corollary and its chart/site-comparison consequences are not dependencies.

The source read was `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md`, especially paragraph 2. I also read `sk-prop-an/lem-amb-affine-space-top-trace.proof.md`, `sk-prop-an/def-amb-vector-integration.proof.md`, and `sec-six-functors-basics/sk-lem-geo-affine-local/cor-amb-affine-space-adjunction.proof.md`. The unit is `sk-prop-an`: its Steps 6 and 7 require ordered iteration and then degree-zero descent. These are preserved. The unit itself is not the delivered key node, so no unit record is edited.

The new lemma isolates a genuine map identification, not a clause of the item: its objects are arbitrary complexes on affine-space bases, and its assertion is coefficient tensor linearity of a fixed counit. It asserts neither vector-bundle descent nor a base-change/direct-sum equation. Its future proof should start with the explicit projective-line coefficient counit, use the open-counit tensor identity, and induct on the coordinate tower. The existing compact-support tensor composition and tensor-action equations identify the successive projection maps. This is the comparison hidden by “same iterated counit” in the blueprint. It is not claimed elementary or already proved here.

## Not duplicates

lem-pur-ordinary-affine-counit-tensor-normalization vs lem-pur-affine-ordered-integration-transposes: the existing statement fixes k algebraically closed over a finite field and A=O_E/varpi^n, with bounded constructible finite-Tor inputs and site/exceptional-transpose conclusions; the new lemma treats arbitrary finite A and Noetherian S and the ordinary-etale explicit counit at every unbounded K. The existing statement cannot be specialized to this domain.

lem-pur-ordinary-affine-counit-tensor-normalization vs lem-pur-ordered-affine-transpose-projection: the existing statement concerns the pro-etale constructible exceptional transpose for the fixed purity coefficient stages; the new assertion concerns the explicit ordinary-etale coordinate adjunction without those restrictions.

lem-pur-ordinary-affine-counit-tensor-normalization vs lem-pur-affine-coefficient-counit-normalization: the existing statement's ordinary-etale counit clause is rank one, over a separated finite-type k-scheme, for the fixed coefficient stages and ctf H. It does not give arbitrary dimension/base/ring/complex.

lem-pur-ordinary-affine-counit-tensor-normalization vs lem-amb-affine-space-top-trace: the existing trace statement evaluates the ordered counit at the coefficient unit and proves its isomorphy/base-change compatibility. The new lemma identifies that counit at arbitrary K with the specified projection expression.

lem-pur-ordinary-affine-counit-tensor-normalization vs cor-amb-affine-space-adjunction: the existing statement is existence of the ordinary unbounded affine-space adjunction, without the coefficient counit equation. The new lemma fixes the coordinate adjunction and states an equality of its actual maps.

lem-pur-ordinary-affine-counit-tensor-normalization vs lem-amb-vector-integration-tensor-counit: the latter assumes a dualizing tensor map invertible and concludes invertibility of an adjunct. It does not identify the actual explicit coordinate counit at K with its unit trace expression.

lem-pur-ordinary-affine-counit-tensor-normalization vs lem-amb-affine-trace-line-counit-iso: the latter's quantified conclusion is IsIso of the affine-line counit; its prose proof mentions the tensor identification but its statement supplies no arbitrary-dimension equation.

Searches of the whole imported blueprint used `blueprint_refs.py search` for vector bundle, integration, affine-space, ordered, counit and projection; DAG keyword searches and the candidate statements above were read. There is no new Stacks tag, so there are no same-tag candidate pairs. The new source is the current blueprint's last affine-space trace paragraph. No restricted pro-etale node was silently treated as an ordinary-etale arbitrary-base theorem.

## Review by Q96

I read the item and each cited statement, not their dependency lists alone. The current blueprint proof explicitly asks to compare the specified maps, trivialize both summands simultaneously, and descend equalities through degree-zero sheaves. The new node states exactly the coefficient counit identity required when the inner rank-r adjunction is evaluated at W_p. It retains N>=1, finite A killed by N, N invertible on a Noetherian S, d>=0, ordinary Tate lines and the proper/open normalization; it introduces every object and has no proof or proof-dependency list.

Step 1 uses the actual definition of integration on any frame and its affine trace, not just an abstract existence isomorphism. Noetherianity of open subschemes is supplied by the existing Mathlib leaf, so intersections need not be affine. The degree-zero gluing statement supplies both concentration and the canonical heart identification; local inverse sheaf maps glue to prove invertibility of the actual trace. This applies to each bundle with its own Noetherian base.

Step 2 uses the definition's inverse-coordinate-square convention. The equation phi_j^{-1}=phi_i^{-1}a_g fixes the direction B_j=rho_g B_i, avoiding an inverse-frame error. The compact-support comparison statement really includes pasting and identity squares, Tate pullback includes composition, and linear invariance really says t rho_g=t over arbitrary Noetherian schemes, including nonaffine overlaps.

Step 3 uses the full affine trace base-change equation for arbitrary morphisms of Noetherian bases, rather than just its isomorphism clause. Pullbacks of the frame opens cover B' and are Noetherian opens of B'. Exchange pasting and Tate composition give the exact l in the item. Exact inverse image puts g^*C_pi in the heart, so the equality is genuinely detected by the existing degree-zero map-gluing theorem; there is no false appeal to descent of arbitrary derived maps.

Step 4 first identifies Sym(F+G) with the algebra coproduct by the universal property on generators, then uses relative-Spec anti-equivalence to obtain the total-space product and its stated projections. These two generic algebraic-geometry statements were opened and added as explicit citations. It then expands the composite-adjunction counit expression. The same ordered string of line counits occurs in either block parenthesization, with the same compact-support compositor by its associativity and identity equations. Tate additivity is supplied by ordinary-etale finite-twist pullback/tensor compatibility. Thus no unproved symmetry of arbitrary exceptional functors is used. Step 5 applies the new coefficient-counit statement exactly at K=W_p, on the Noetherian coordinate base A^s_U. It needs the actual inverse projection, which the proper projection and open tensor theorems make invertible. This new dependency is a comparison problem, not a relabelled direct-sum clause.

Step 6 checks restriction of P using the existing arbitrary-base coefficient-first projection/exchange equation. The compact-support compositor/exchange coherence identifies the source, and Step 3 identifies the restricted q trace. The tensor composition statement explicitly includes refinement comparisons. The common source is degree-zero since alpha identifies it with C_h. Therefore gluing is applied on its stated domain and proves equality of the actual maps for every normalized compactification triangle.

Step 7 uses linear invariance for the block permutation; its shifts are even and the sign is (-1)^(4rs)=1. The Tate tensor permutation can also be checked on a local generator of the rank-one Tate line. Rank zero uses the identity adjunction, not a positive-rank induction hypothesis. Empty bases give zero sheaves and unique arrows. The new lemma likewise passes d=0 (unit projection/identity counit), K=0, empty S, and N=1 (only the zero ring). A general test coefficient ring such as Z/4 with N=4 has no flat coefficient-change assumption: there is no change of coefficients in this task.

For B1--B10 and C1--C8, I checked self-contained objects, single TeX escapes, unchanged source/import metadata, exact statement quotations, no hidden use of a cited proof, and no cycle through the parent. All proof steps are shorter than 2,000 characters. The new node has four logged search kinds and two semantic phrasings. Search hits are ordinary sheaf adjunctions, coalgebra counits, GammaSpec, ring traces and ring-theoretic etale lemmas; none gives this etale compact-support equality. The item searches are also recorded as run. No Mathlib leaf or finished proof was overlooked among those hits.

## Unfinished work

Only the new statement-only counit-normalization lemma is left unsplit, as required by one-level splitting. The mathematical dependency is explicit. No Lean was written and no compiler or Lake command was run. Mechanical dry-run results are recorded below when complete.

## Dry-run repairs

The first dry run exited without pushing because some literal quotations were shorter than its 40-character minimum. I replaced those by substantive statement passages and checked all quotations as literal substrings. The self-review also made the symmetric-algebra product argument explicit in Step 4, citing the existing universal-property and relative-Spec statements. No new mathematical node was needed for that argument.
