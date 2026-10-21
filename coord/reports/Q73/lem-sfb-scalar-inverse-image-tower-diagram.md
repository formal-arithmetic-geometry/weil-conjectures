# Stage-1 worker report: lem-sfb-scalar-inverse-image-tower-diagram

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scalar-inverse-image-tower-diagram.json`: statement; split into five proof steps; unchanged statement, statement dependencies and provenance. No exact Mathlib match.
- `citations.json`: thirteen verbatim statement quotations, one for every step/node citation.
- `report.md`: this report.

No new nodes, no Mathlib leaves, no Lean changes, and no unit or chapter changes. `searches.jsonl` is the search command's own log. The sandbox script `write_split.py` only prepared the sandbox JSON and citation manifest.

## Attachments

None. Searched the live `lean/WeilConjectures/` tree for the blueprint tag, scalar inverse-image/tower terminology, balanced coequalizers and `extendScalarsComp`. The ordinary scheme-module `pullbackComp_tensor` in `AlgebraicGeometry/PullbackTensorComposition.lean` concerns geometric composition and a tensorator; it does not state this arbitrary-topos coefficient-tower square. `Mod.extendScalarsComp` supplies scalar reassociation alone, not its compatibility with the specified inverse-image quotient comparison. No complete project declaration states every clause of the item.

## Literature wanted

None.

## Problems found and changes made

The imported item was a true, well-typed statement with no proof. Its parent blueprint proof, `main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md` (3), only says that canonical tensor identifications respect scalar reassociation. I supplied that calculation before localization. There is no statement dispute, no replacement of the unit route, and no additional hypothesis.

A tensor pairing is not generally surjective on sections, and an arbitrary topos need not have enough points. The proof therefore does not infer equality from that assertion. Step 3 proves an injectivity test by adjunction: first transpose along the underlying geometric adjunction, then use the two actual extension/restriction adjunctions, whose composite unit is `m ↦ 1 tensor (1 tensor m)`. Naturality of the geometric unit transports that test upstairs. This is a short argument from the cited adjunctions, rather than a new lemma node that would duplicate elementary work.

The normalized inverse-image tensor theorem and the extension/restriction adjunction already have nodes. I reused them, and recorded the generic normalized comparison as an off-unit tool use. No new statement-only nodes were needed. Both balancing checks, the two inverse maps, coefficient linearity and the two composite calculations remain steps of this item's proof.

## Searches and route

Read `dag/chapters/sec-six-functors-basics.json` and `dag/units/sk-prop-scalar-six.json`, and followed the unit's pullback/coefficient-comparison route. The ordinary square serves the final sentence of parent proof (3), as recorded in `blueprint.from.place` and `split_report.blueprint`. This is not the unit's key statement, so no realization record changes are appropriate.

Searched the entire DAG for Tags 03EL and 03EK and for balanced coequalizers, inverse-image tensor comparisons, scalar towers and reassociation. Ran `tools/blueprint_refs.py ancestor` for the item and blueprint searches for `inverse image tensor`, `scalar tower`, `balanced`, `reassociation`, `inverse-image scalar` and `tensor comparison`. No imported blueprint node states this square in another form, so `blueprint.same_as` is empty. Existing inverse-image comparison nodes were reused rather than duplicated.

Ran the mandated `msearch.py` searches with LeanFinder, LeanSearch, Loogle and grep, followed by a second semantic phrasing with LeanFinder. All five results are in the command's log and appended, without altering the item's inherited Q20 search records. Read the candidate definitions in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` (pullbackComp around line 170, pullback_assoc at 193) and `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean` (extendScalarsComp at 984, its unit formula at 1006 and extendScalars_assoc thereafter). The former assumes continuous site functors and states associativity of geometric pullback comparisons; the latter concerns ordinary modules over rings. Neither is the specified equality for an arbitrary geometric morphism and sheafified balanced tensor, and combining them would require the normalization argument, not a one-line specialization. The second LeanFinder phrasing returned presheaf tensor maps and generic coequalizer tensor lemmas, rather than this square.

## Unfinished work

None in the one-level stage-1 split. This delivery makes no claim to a Lean proof or a derived comparison theorem.

## Review by Q73

I read the current parent blueprint proof (1) and (3), Stacks `sites-modules.tex`, Tag 03EK (`section-tensor-product`, including its bilinear representing property) and Tag 03EL (`lemma-tensor-product-pullback`, including the Hom/Bilin argument). I also read `lemma-pullback-module` (Tag 03D2), the following `lemma-adjoint-push-pull-modules`, and `sites.tex` Tag 00YV (`proposition-functoriality-algebraic-structures-topoi`). These supply the ordinary inverse-image structures and explain why the calculation is valid for morphisms of topoi, not just maps of spaces or continuous functors presenting sites. No SGA source is used. Since the parent blueprint's last compatibility sentence has no detailed proof, the expanded proof is honestly marked agent-written. There are no new nodes whose statements need a separate source audit.

For step 1, I opened the actual statements of `def-weil-pbc-algebraic-inverse-image`, `lem-weil-pbc-algebraic-inverse-image-tensor-comparison` and `def-weil-pbc-ringed-tensor-section-calculus`. The first gives transport of multiplication, addition, units and module actions under the finite-product comparison, the second gives the normalized comparison on arbitrary generalized pure pairings, and the third fixes the actual pure pairing, its uniqueness property and the scalar adjunction unit. Apply the comparison with r-modules s and M; r acts on s by the given ring map. Its first-factor s-linearity follows by checking the same multiplication map on the pure pairing, not from an assertion that an arbitrary r-linear isomorphism is s-linear. The given geometric inverse image preserves finite limits and the sites satisfy the common universe hypotheses. These cited statements really give the formulas used here.

For step 2, I read `def-pur-sheaf-tensor-product` and the tensor-section-calculus statement. The former is the sheafification of sectionwise balanced tensor, and the latter gives its actual pairing and extension adjunction. I checked the B balance and the inner A balance explicitly: the first multiplies by b(beta) in C, and the second uses the composite b a, exactly as the statement requires. The inverse's composite moves b' from the inner B factor to C by the outer balancing relation. Thus this is an elementary quotient calculation, not an unproved scalar-tower lemma hidden in a new node. Naturality is substitution in the final module argument.

For step 3, I opened `def-weil-pbc-ringed-topos-morphism`, the algebraic-inverse-image definition and the tensor-section-calculus statement. The first includes the underlying sheaf adjunction and the induced direct-image module action; the second ensures those actions are the transported ones; the third explicitly states extension/restriction adjunction and its unit. The adjunct of a C_X-linear map is C_Y-linear by naturality of the sheaf unit with respect to the action and addition maps. Composing the two scalar Hom bijections therefore tests it on precisely the composite of the two scalar units. The displayed naturality equation then reduces this test to the upstairs composite with F(w_Y). This short chain of injective Hom comparisons proves the criterion inside the step. In particular I did not use the more specialized continuous-site multimap lemmas as though they covered arbitrary geometric morphisms.

For step 4, the cited algebraic transport, normalized comparison and tensor calculus give exactly the unit insertions used in the two routes. The left composite gives the AC unit. The right composite first inserts the C unit, then replaces the AB unit by its actual inverse-image unit, then applies t_X, again obtaining the AC unit. I also checked the arbitrary coefficient formula: both routes give c b_X(b') tensor m. This explicitly verifies the final C_X action and fixes the orientation of every comparison. Step 3 then upgrades the unit calculation to equality of the two C_X-linear maps. It is not an argument that merely declares canonical maps coherent.

For step 5, the tensor calculus supplies naturality in the module map, and `def-weil-abstract-derived-category` explicitly says that complex morphisms are degreewise morphisms commuting with the differentials. Equality for every M is equality of the natural transformations; substituting each differential gives the termwise complex statement. There is no tensor total complex, K-flat preservation, derived existence theorem or sign convention to assume.

I checked the small cases of identity h, identity coefficient arrows, M=0, zero coefficient rings, the nonflat tower Z → Z/4 → Z/2 on a one-point topos, and degenerate sheaf topoi. Every formula remains valid; it never divides by a coefficient or asks for tensor exactness. The ring and site symbols in the imported statement are overloaded, but their types distinguish them and no mathematical correction is needed.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the delivery: there are no new nodes; the existing definitions and the normalized comparison say the exact facts cited; no source proof rather than statement is used as a black box; all additional arguments are written out as elementary steps; and no clause is transferred to a fresh node. The generic off-unit theorem is declared in split_report.tool_uses, without modifying the maintainer-owned top-level tool_uses. Every step is shorter than 2000 characters. Each of the thirteen citations has an exact substring quote in citations.json. The item statement and its statement dependencies remain unchanged.
