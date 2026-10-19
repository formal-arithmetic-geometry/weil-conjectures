# Repair of lem-weil-delta-proper-pushforward — Q61

## Files written

- `dag/nodes/sec-six-functors/lem-weil-delta-proper-pushforward.json`: repaired item, statement and Lean record unchanged; eleven proof steps, longest 1221 characters.
- `dag/nodes/sec-six-functors/lem-sf-internal-adjunction-hom-chain.json`: new statement-only auxiliary lemma; Mathlib searches found no match.
- `dag/nodes/sec-six-functors/lem-sf-internal-adjunction-test-arrow.json`: new statement-only auxiliary lemma; Mathlib searches found no match.
- `dag/nodes/sec-six-functors/lem-sf-internal-adjunction-projection-comparison.json`: new statement-only auxiliary lemma; Mathlib searches found no match.
- `citations.json`: verbatim statement quotations for every node cited by every item step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the blueprint tag, by the item name, and by the exchange/double-dual terminology. No sorry-free declaration states this item or any of the three extracted auxiliary statements. The existing TensorHom declarations concern exchange maps but do not state the required proper-etale evaluation formulas.

## WANTED

None.

## Return repaired and comparison with current repository

The shared item had one non-elementary 2574-character step 4. I restored that current head, retained its statement, dependencies, source, import fields, Lean record, and proof route, and replaced that step by the original short definition step followed by three separate short applications. The hidden arguments are now their own nodes: the internal-adjunction Hom-chain, the counit computation on a test arrow, and the comparison of the projection expression with the direct-image product pairing. A final short step specializes these statements to the dualizing object and invokes the existing internal-adjunction isomorphism. The later naturality, double-transpose, and final implication arguments remain unchanged apart from step references. The deleted temporary combined lemma was redundant with these three nodes. On the resumed repair I also corrected a stale final reference from Step 7 to Step 10 and introduced the generic notation explicitly in Step 5.

No statement dispute was found. The conclusion remains invertibility of the pushed-forward double-dual arrow and does not assert that direct image reflects isomorphisms. No constructible, pro-etale, perfectness, or geometric-biduality hypothesis was added.

## Sources and searches

I read the item source `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-weil-delta-proper-pushforward.md`, the corresponding proof text in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-biduality-general/`, and the three cited node files in the sandbox. The three new nodes each point to the exact sentence “The isomorphism of [prop-asd-internal-adjunction] is exactly the adjoint of this pairing.” The chain, test-arrow formula, and projection/product identity elaborate that assertion; the source itself does not write their formulas. Each new statement introduces finite coefficients, a proper finite-type morphism, Noetherian schemes with finite affine covers, and ordinary unbounded etale module derived categories. Invertibility on the schemes is not needed for these formal auxiliary statements, consistently with the cited proper projection node.

For the Mathlib audit I ran LeanFinder, Loogle, grep, and LeanSearch for each new node. The returned declarations (`CategoryTheory.expComparison`, `CategoryTheory.ihom.ihom_adjunction_counit`, `ExponentiableMorphism` counit identities, and generic projection/counit facts) require Cartesian monoidal structures, slice categories, or unrelated sheaf settings; none states the proper ordinary-etale derived formulas. Their queries and results are recorded in each node's `mathlib_searches` and in the command log. The first resumed dry run found three recorded Loogle queries absent from the retained log. I ran all three and read their actual results: zero hits with an unknown-identifier diagnostic, one cartesian Frobenius-mate hit, and zero hits, respectively. The Hom-chain node also retains the valid logged `"expComparison"` query, so it does not rely on the malformed query. I corrected grep query text to the exact logged regex, retained the directory separately, corrected a mismatched LeanSearch hit summary from the actual log, and reused the second semantic phrasing already logged in the previous attempt. New-node TeX escapes and literal newline escapes were normalized before regenerating their exact citation quotes.

## Not duplicates

lem-sf-internal-adjunction-hom-chain vs prop-asd-internal-adjunction: the existing proposition gives the canonical internal-adjunction isomorphism, while this node records its test-object Hom-chain characterization through the proper projection map.

lem-sf-internal-adjunction-test-arrow vs prop-asd-internal-adjunction: the existing proposition gives only the comparison isomorphism; this node states the explicit inverse-transpose formula with both counits and evaluation.

lem-sf-internal-adjunction-projection-comparison vs lem-amb-proper-coproducts-projection: the existing projection node gives projection invertibility and its basic symmetry, while this node proves the equality between the test-arrow expression and the lax product map.

lem-sf-internal-adjunction-projection-comparison vs lem-kun-inverse-image-monoidal: monoidality of inverse image supplies a comparison used in the adjunct calculation; it does not state the resulting equality for proper direct image.

Each new node is strictly auxiliary and contains no double-dual conclusion, so none restates the item.

## Review by Q61

I checked every item step against the cited node statements and its source. Step 1 uses the locally-Noetherian finite-type result, finite-type and compactification definitions, ambient exceptional adjoints, proper compact-support identification, and unbounded compact-support composition; these supply exactly the Noetherian and adjunction hypotheses claimed. Step 2 uses the three ambient adjunction Hom bijections and the unbounded composition to identify the dualizing objects and define the transported counit. Step 3 uses the unrestricted ringed-site tensor–Hom and global-sections lemmas, the duality-pairing evaluation, and the signed tensor symmetry, so the defining double-evaluation equation is typed for arbitrary complexes.

Step 4 only defines the lax product map, its pairing, and its tensor–Hom transpose using the projection-formula counit and inverse-image monoidality. Step 5 cites the new Hom-chain node, which states the canonical comparison on every test object. Step 6 cites the new test-arrow node, which states the exact expression with the ordinary counit `epsilon_P`, exceptional counit `c_N`, evaluation, and projection isomorphism. Step 7 cites the new projection-comparison node, whose hypotheses and conclusion identify that expression with `mu`; taking the test arrow to be the identity explicitly identifies the transpose with the canonical comparison. I also corrected the Hom-chain statement to distinguish its ordinary and exceptional adjunction bijections from its two tensor–Hom bijections. Step 8 specializes `M=L`, `N=omega_Y`, uses Step 2's identification to obtain `P=D_X L`, and invokes `prop-asd-internal-adjunction` for invertibility. Steps 9–11 retain the explicit naturality/symmetry calculation, signed double-transpose identity, and the final inverse formula; their cited tensor, duality, and internal-Hom statements say exactly the operations used.

I verified the new-node hypotheses (finite commutative coefficients, proper finite-type map, Noetherian schemes with finite affine covers, ordinary unbounded etale categories, and the two distinct counits) and checked small cases: identity maps reduce to the ordinary evaluation identity; zero complexes give zero maps; finite disjoint unions use componentwise counits; and unbounded nonperfect complexes require no perfectness assumption. I compared all item fields with the current shared node; only proof, proof dependencies, split status, and split report differ. The natural statement, Lean statement, and all other maintainer-owned records agree exactly. I verified that the Hom-chain and test-arrow conclusions contain no double-dual clause, and that the projection/product identity only normalizes the lax product; thus none moves the item wholesale to a child. No proof step exceeds 2000 characters. No compiler, Lake, Lean writing, or live-project mutation was used.

## Unfinished work

The three auxiliary nodes are intentionally statement-only and join the stage-1 queue. No part of this one-level split is left uncompleted. The server dry run and direct delivery use the required deliver.py commands; their terminal results are the validation and delivery evidence.
