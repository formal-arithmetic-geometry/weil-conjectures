# Q98 worker report: lem-sfb-representable-finite-stack-properties

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-representable-finite-stack-properties.json`: item, statement unchanged; five proof steps, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-representable-stack-property-tests.json`: new statement, unsplit; no Mathlib match. This is the general compatibility of stack properties with scheme tests, with no finite hypothesis.
- `citations.json`: ten verbatim statement excerpts for the ten step/node pairs.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the item tag and representable/finite/stack notions. There is no declaration proving the stack assertion. Scheme finite-proper and finite-quasi-finite results already have DAG nodes and are reused, not duplicated. The existing upstream theorem `AlgebraicGeometry.IsFinite.locallyQuasiFinite_and_quasiCompact` only concerns schemes and is not an attachment for this item.

## WANTED

None. The necessary sources are available in the local Stacks checkout.

## Corrections and route

The item is mathematically sound and its statement is unchanged. Its imported source suggests algebraicity followed by unramified diagonal and DM equivalence. In the etale-stack convention actually defined by the dependency, a direct construction is shorter and avoids silently changing the topology of the stack condition: construct the Isom spaces, then explicitly pull back the target's etale scheme atlas. This is the pullback-atlas mechanism of algebraic.tex 05UM, with the Isom interpretation of 045G written out. It retains the finite-cover prerequisite of the ancestor's alteration/moduli route; no unit or chapter route changes.

The chapter and unit records were read. This item is a supporting node, not the key node of the unit, so no realization fields were changed. `blueprint_refs.py ancestor` reports a null ancestor on the present chain. I preserved that existing null and the entire via chain, and used the inherited chain with the item prepended on the new node. Whole-blueprint searches for representable, Deligne, representable diagonal, 05UM, proper representable, 06UA, proper locally quasi-finite and scheme base change found no duplicate of the new compatibility statement. Searches in the whole DAG by these notions and the source tags were also read.

The sole off-unit tool is `lem-trf-space-fibre-products-etale-covers`: its finite-limit assertion constructs the Isom-space equalizer. This does not replace an alteration step and is declared in `split_report.tool_uses`. The existing finite-quasi-finite theorem is Lean closed; finite-proper is already a Mathlib leaf.

## Review by Q98

I read algebraic.tex 045G (lemma-representable-diagonal) and 05UM (lemma-representable-morphism-to-algebraic), including their proofs, and the source definitions of 2-fibre products and DM scheme atlases in `def-sfb-stable-pointed-moduli-groupoids`. I also read stacks-morphisms.tex 050E, 050L and 06N3 to check the seeded route, but these are not used as uncited black boxes: the constructed atlas directly satisfies the definition. For the new node I read 04YS (lemma-representable-separated-diagonal-closed), 06UA (lemma-representable-by-spaces-quasi-finite), 06PU (definition-locally-quasi-finite), and the compatibility discussion immediately following 0CL5 (definition-proper), which explicitly states the representable compatibility. The new node specializes that general compatibility to scheme-representable maps between DM stacks. Its properness definition includes finite type and proper diagonal; its local-quasi-finite definition includes local finite type, quasi-DM diagonal and discrete field fibres. It does not conflate Mathlib's potentially weaker `LocallyQuasiFinite` predicate with Stacks' notion.

In step 1 the existing DM Isom-space theorem explicitly supplies the algebraic space I for arbitrary objects over any T; its unramifiedness is unused. The finite test hypothesis supplies the actual scheme P, and the scheme-as-algebraic-space definition permits using it as an algebraic space. The maps a and b use the inverse of the universal isomorphism in exactly the orientation required by the 2-fibre-product arrow formula. No finiteness, nonempty-fibre or smoothness condition on T is used.

In step 2 the cited algebraic-space fibre-product theorem really states existence as an algebraic space for arbitrary maps, so it applies over the scheme T to I, P and the scheme P times_T P. The identification with Isom_Y is written on every test scheme: equality in the represented discrete P means precisely an isomorphism beta above the specified alpha. Its uniqueness follows from representability of P, not from trivial inertia of X or Y. Conversely beta gives that equality. This is an elementary identification from the fibre-product definition and the cited existence theorem, not an independent descent or representability theorem hidden in the text. A scheme pullback of the diagonal of Y is this Isom functor, by the same definition.

In step 3 I checked that the finite hypothesis gives V as a scheme; it does not make V to U etale. Instead V to Y is etale and surjective because each scheme test is the corresponding test of the already etale surjective atlas U to X. Associativity of the 2-fibre product is explicit composition of its isomorphisms and has an explicit inverse. The cited definition supplies exactly the representability, etaleness and surjectivity tests needed, together with the DM conclusion after step 2. Thus this step needs no unrecorded descent result and assumes no flatness or surjectivity of v.

In step 4 the statements of the two cited scheme theorems are literally finite implies proper and finite implies quasi-finite. The definition node supplies the local quasi-finite meaning. I read their statement records and checked the local proper/finite and quasi-finite source references, as well as spaces-morphisms.tex 04NZ and 04NY, which reduce to the scheme results. In step 5 both source and target are DM, scheme representability is a hypothesis, and step 4 verifies every scheme test of both equivalences in the new node. The step uses the statement of that node, not anything inside an unsplit proof.

For B1--B10 I checked that the new node introduces S, both stacks, f, every scheme T, its represented pullback and the projection; all nonprimitive notions are cited or defined inline. It has no proof or proof dependencies. There is only one new supporting theorem, not a restatement of finite implies proper or of DM inheritance. The same-tag pairs are distinguished below. All Mathlib queries recorded on it were actually run using msearch.py, including two natural-language phrasings and a grep, and the results were read. The returned scheme properness and quasi-finiteness declarations do not establish the comparison with stack diagonals and stack point topology. I read the actual Mathlib Proper and QuasiFinite sources to check this boundary. The unrelated generic diagonal-representability searches were exploratory and were not converted into a needless new node.

For C1--C8 every non-elementary assertion is a cited existing theorem or the single new compatibility theorem; the two-fibre-product identifications and atlas tests are explicit elementary steps. Every cited statement was opened and its used passage is copied verbatim in citations.json. There is no use of a cited node's proof. No circular appeal to the finite-cover/coarse-space parent appears. For D1--D5 the actual argument remains in the item: the new node contains neither the finite hypothesis nor the construction of Y's atlas. For E1--E7 I checked arbitrary bases, nonreduced tests and the orientation of the Isom maps; no separation or Noetherian assumptions on S or X enter. No source error or statement dispute was found. Every proof step is below 2000 characters.

Small cases checked: the empty cover gives an empty source atlas and both properties; the identity map gives the existing atlas and an identity Isom equalizer; a nonreduced finite fibre (for example dual numbers over a field) is allowed because the atlas is pulled back in the other direction. For the new compatibility statement, identity maps and empty scheme-representable morphisms satisfy both sides, while a nonproper open immersion does not pass the properness tests. A positive-dimensional scheme over a field fails the local-quasi-finiteness tests on both sides. A nonrepresentable classifying-stack map is excluded, so discrete singleton point spaces alone are never used to infer local quasi-finiteness.

## Not duplicates

lem-sfb-representable-stack-property-tests vs lem-sfb-representable-finite-stack-properties: the item proves DM inheritance and two properties from scheme-test finiteness; the new node assumes both stacks DM and compares each property with its scheme tests, without finiteness.

lem-sfb-representable-stack-property-tests vs lem-sfb-stack-proper-locally-quasifinite-composition: the existing node proves composition and comparison for maps between algebraic spaces, not the scheme-test criterion for arbitrary scheme-representable morphisms between stacks.

lem-sfb-representable-stack-property-tests vs lem-sfb-dm-coarse-proper-locally-quasifinite: the existing node proves properties of a specific generally nonrepresentable coarse moduli morphism, not a representable comparison theorem.

lem-sfb-representable-stack-property-tests vs lem-sfb-inertia-free-finite-cover-coarse: the existing node uses the representable finite input and coarse moduli to deduce scheme finiteness under trivial geometric inertia; it does not state either test equivalence.

## Unfinished work

No part of this one-level split remains unfinished. The new compatibility lemma is intentionally statement-only and will be split as its own later item. No Lean was written or compiled. Server dry-run and push results are recorded after validation.
