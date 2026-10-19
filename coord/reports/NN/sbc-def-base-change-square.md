# Stage-1 report: sbc-def-base-change-square

## Files written

- dag/nodes/sec-smooth-base-change/sbc-def-base-change-square.json: existing definition, split using the two existing statement dependencies; no full Mathlib match.
- citations.json: empty list, since definitions have no proof steps.
- No new nodes and no Mathlib leaves.

## Attachments

None for the item. AlgebraicGeometry.Etale.squareUpperStarIso already belongs to def-weil-pbc-cartesian-square. I read Square.lean:74–79 and the pasting declarations cited in that node's audit. The comparison alone does not package the chosen Cartesian identification, so I do not claim an attachment for this entire item. The upstream master was used only as read-only reference, not evidence of completion.

## Sources and searches

The item source read was literature/blueprint/master/blueprint/sec-smooth-base-change/sk-def-bc/sbc-def-base-change-square.md, its whole definition. I also read the sec-smooth-base-change chapter and sk-def-bc unit records. The unit defines the base-change property; this item is only its square datum, not the unit's key statement, so no unit realization is changed.

I read def-weil-pbc-cartesian-square and its blueprint source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/def-weil-pbc-cartesian-square.md. I read the entire statement of def-weil-pbc-scheme-conventions. The former explicitly supplies a chosen identification, commutativity, and the canonical inverse-image comparison with identity/pasting compatibility; the latter supplies the scheme/morphism conventions. No Stacks theorem is newly used: this is a definition already specified by the blueprint, with its notions delegated to those existing nodes.

DAG and blueprint searches used the square's id, cartesian square, inverse-image, and the existing dependency id. The generic Cartesian-square node states the same datum with different corner names, so blueprint.same_as records it. No new duplicate is created.

Mathlib searches were run through msearch.py and copied from searches.jsonl. The first grep used Mathlib/AlgebraicGeometry as a subdirectory and returned no hits; a second search used AlgebraicGeometry/Sites and returned the site files. The first Loogle query had an unknown identifier and is recorded as invalid rather than evidence of absence; the second, CategoryTheory.IsPullback, found the general Cartesian square API. The two LeanFinder phrasings returned affine pullback formulae, open-immersion restrictions and over-site composition. None supplies this full small-etale definition. LeanSearch was unavailable (HTTP internal server error), recorded as unavailable. Generic IsPullback is only a partial match because the item also specifies inverse-image comparison and coherence.

## Problems and corrections

The statement is correct; no STATEMENT-DISPUTED and no route change. The only convention to check carefully is orientation: setting (X_prime,X,Y_prime,Y)=(Y,X,T,S), (g_prime,f_prime,f,g)=(h,e,f,g) in the existing Cartesian-square node gives e^{-1}g^{-1} to h^{-1}f^{-1}. The item's theta is its inverse. Inverting a coherent comparison retains identity and pasting compatibility, with the order of composition reversed as required. This is an explanatory check, not a new theorem node. The two statement dependencies are unchanged. The imported same_as was unset; it is now filled. The item is a definition, so proof and proof_deps remain empty, and no proof-origin is invented.

## Unfinished work

None at this one-level split. Its existing notion dependencies remain under their own ownership. No Lean was written or compiled and no agents were started.

## Not duplicates

No new nodes. The item is the named square convention of the smooth-base-change unit, with the same Cartesian datum as def-weil-pbc-cartesian-square and the inverse orientation of its comparison. This is recorded in blueprint.same_as rather than duplicated into another node.

## Review by NN

I checked B through E of delivery-errors against the source and the two node statements. For B, there are no newly created nodes, no incomplete stand-alone statements, and no claimed Mathlib leaf; searches are actual logged calls and the unavailable search is distinguished. For C, there are no proof-step citations requiring quotes: the statement dependencies themselves were read in full. The Cartesian-square statement says precisely what is taken from it, including coherence, rather than merely defining the geometric diagram. The conventions statement supplies scheme morphisms, without imposing finite type, properness, quasi-compactness, quasi-separatedness or coefficient assumptions. For D, this is a definition split by exposing its notions, not a theorem whose argument was moved into a clause node. No dependency was invented and no cycle was added. For E, I verified the corner substitution and the opposite orientation above. Identity squares give identity comparisons, and taking inverses of a pasted comparison gives the reversed composite of inverse comparisons, so the direction change does not lose the coherence clause. Empty schemes and arbitrary morphisms are allowed; none of these constructions require nonempty schemes, proper morphisms or invertible torsion. The inverse-image category remains the existing small-etale category, not a silent identification with a pro-etale or condensed coefficient category. I retained the source statement and repaired only status, search records and blueprint cross-reference metadata. No mathematical fact is imported from a node's proof.


## Second reading by NN

- Item statement: checked every corner, arrow, chosen Cartesian identification, commutativity and comparison against the complete blueprint source `sec-smooth-base-change/sk-def-bc/sbc-def-base-change-square.md`; PASS, with no extra finiteness, smoothness or coefficient hypothesis. This source has no Stacks tag or lemma label to inspect.
- Statement dependency `def-weil-pbc-cartesian-square`: read its complete node statement and its blueprint source's Detailed form; PASS. Substitution $(X',X,Y',Y)=(Y,X,T,S)$ and $(g',f',f,g)=(h,e,f,g)$ gives $e^{-1}g^{-1}\cong h^{-1}f^{-1}$; its inverse is exactly the item's comparison.
- Statement dependency `def-weil-pbc-scheme-conventions`: read the complete node; PASS. It supplies schemes and morphisms through its definition pointers and does not assert those morphisms are proper, finite type or quasi-compact. Inverse image is supplied transitively by the Cartesian-square node's `def-weil-pbc-inverse-image` dependency, whose complete statement was also read.
- Proof steps: none; PASS against stage 1 section 3(2), which splits a definition by its notions. Empty `proof`, `proof_deps` and `citations.json` correctly assert no theorem proof or step citations; no unquoted non-elementary result is used.
- New nodes: none; PASS against B1–B7 and C5/D1. Repository searches for Cartesian squares and the inverse-image expressions found the existing generic definition; there is no smaller fact to create or duplicate to remove. The existing comparison declaration in `Square.lean` lines 74–79 and horizontal/vertical pasting statements in `Pasting.lean` lines 154–173 and 240–260 were opened; their statements agree with the generic node's comparison, without themselves supplying the chosen pullback datum. No attachment for the entire item is justified.
- Edge cases and coherence: PASS. Identity squares give the identity after the unit identifications. For any pasted comparison written as a composite of invertible maps $c\circ b\circ a$, its inverse is $a^{-1}\circ b^{-1}\circ c^{-1}$: composing in either order cancels each adjacent inverse. Whiskering preserves inverse equations because functors preserve composition and identity; thus inverting the existing pasting identities gives precisely the comparison in the item's orientation, including the associativity/composition identifications. Empty schemes, identity squares over a field and the zero sheaf require no exception. Degrees and coefficient integers do not occur in this datum, so $q=0$ and $n=0,1$ impose no restriction on it.

Changes made:

- Appended this independent second reading, making the inverse-pasting check explicit instead of leaving it as “compatibility is inherited”. Retained all first-worker sections and the correct node statement and dependencies.
- Ran a fresh Loogle search for `CategoryTheory.CommSq`, distinct from the first reader's pullback queries, and recorded its actual eight logged leading hits in the item. Its declaration gives commutativity, not the full Cartesian datum; it is a partial match, not a Mathlib leaf. The additional query is preserved in `searches.jsonl`.
- No mathematical repair, statement dispute, new node, Mathlib leaf or citation change was needed. No Lean was written or compiled, and no agent was started.
