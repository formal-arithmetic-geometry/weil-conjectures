# Q86 stage-1 report

Item: lem-pod-frobenius-pullback-monoidal-adjunction-coherence.

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-frobenius-pullback-monoidal-adjunction-coherence.json`: existing statement node, now split in nine steps. No Mathlib match for the complete item.
- `citations.json`: 18 verbatim supporting quotations, one for each step/node citation.
- `report.md`: this report. The required search command also wrote `searches.jsonl`.

There are **0 new nodes and 0 new Mathlib leaves**. Every non-elementary ingredient already has a suitable node. The imported statement, statement dependencies, source, creation metadata and blueprint ancestry are retained. No unit/chapter record is changed: this is not the unit's key node.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and Frobenius/monoidal/adjunction notions. There is no declaration carrying the item tag. `WeilObject/BoundedConstructible/UpperLowerStar.lean` provides separate operation lifts, but not all the requested comparisons and coherence equations. `WeilObject/BoundedConstructible/TensorHom.lean:89-107` defines `weilTensorComparison` with `sorry` in its naturality proof. The generic `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction` is a useful existing categorical tool; it does not by itself identify this project's specified coefficient operations or prove their tensor/composition equations. The existing DAG node `lem-sf-fixed-pair-adjunction-lift` already records that tool, so no new attachment node is made.

## WANTED

None. The argument uses the available blueprint, Stacks sources and the project source of the generic fixed-pair adjunction theorem; no SGA source is used.

## Findings and corrections

The live item had no proof and was unsplit, and the sandbox had no earlier item, report or search log. There is no statement dispute: the stated restriction to full constructible domains and the distinction between ordinary and exceptional adjunctions are necessary and are retained. The proof makes the blueprint's abbreviated pullback/tensor and ordinary-adjunction argument explicit. In particular it checks the direction of the mate: the square transformation is the inverse of the pullback Frobenius comparison. It does not infer invertibility for an arbitrary mate.

Mathlib searches were run with the required Q86/item command using leanfinder, loogle, grep and leansearch, with a second semantic phrasing. All five searches were available. Their exact query strings and hit summaries are in the node and the command's `searches.jsonl`. The item's inherited Q12 search entries remain as history; the appended entries are the searches actually run by Q86. Read Mathlib `CategoryTheory/Adjunction/Mates.lean:125-151`, `CategoryTheory/Endofunctor/Algebra.lean:470-495`, and `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:155-184` for the relevant hits. The latter treats ordinary sheaves of modules, the algebra/coalgebra equivalence has a different assertion, and the mate lemmas handle only a formal part of this item. The second leanfinder query also returns lifting-property and shift statements; none supplies all the requested rational/common-stage constructible Weil coherence. Thus the item is not a Mathlib leaf.

## Unfinished work

None within stage 1. This delivery does not claim that the cited unsplit or sorried project statements have been proved in Lean. It supplies the requested one-level split using their statements.

## Not duplicates

No new nodes are proposed. Whole-DAG and blueprint searches included `Frobenius coherence`, `pullback composition` and `Weil pairs`, together with fixed-pair adjunction and monoidal/pullback associativity searches. Existing integral composition, scalar-extension, tensor-comparison, semilinear-operation and abstract adjunction-lift nodes are reused. The larger `prop-weil-operations`, `lem-fix-weil-operations` and `lem-pod-constructible-mate-coherence` lie above this item and are not cited as proof dependencies. The native derived-Weil nodes use a derived category of equivariant sheaves, rather than fixed pairs in the specified constructible derived category, and cannot replace this argument. Before writing, a dependency traversal checked that the selected theorem nodes do not reach this item, so their use does not close a cycle.

## Review by Q86

I read the chapter and unit records, the three-level rule in SETUP, the live item, `prop-weil-operations.proof.md` sentence 1, and the first two paragraphs of current-main `lem-fix-weil-operations.proof.md`. I also read Stacks `sites-cohomology.tex`, Tag 0D6D (`lemma-derived-pullback-composition`), Tag 07A4 (`lemma-pullback-tensor-product`), and Tag 07A7 (`remark-base-change`). Their K-flat tensor/composition constructions and counit-transpose definition support the chosen normalization, not an arbitrary isomorphism of endpoints. For the abstract adjunction step I read `lean/WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebraAdjunction.lean:38-125`. No new nodes need a separate source review.

I opened the statement of every cited node and checked the use step by step:

1. `lem-pod-semilinear-field-operation-lifts` supplies the canonical Frobenius comparisons, their standard lift formula and equivalences without absolute separatedness; `lem-pod-integral-pullback-composition` supplies the natural comparison c with the chosen direction. Substitution gives s = c(f,gY)c(gX,f)^(-1); naturality verifies the comparison for successively lifted pullbacks.
2. The associativity clause of `lem-pod-integral-pullback-composition` is the precise identity carried to rational coefficients. Clause (1) of `lem-pod-pullback-identities-scalar-extension` states compatibility with the specified scalar-extension comparisons, not mere existence of an abstract iso. `def-weil-derived-pullback-tensor-hom` explicitly defines localization on Hom modules and common-stage arrows by conjugation. `lem-pur-derived-pullback-tensor-iso` itself includes coherence at all coefficient stages. This verifies descent and avoids assuming that an arbitrary rational Weil isomorphism preserves a lattice.
3. I checked all three associativity substitutions, including their sources: (gX,f,h), (f,gY,h), and (f,h,gZ). After precomposition by c(gX,hf), the c(gX,f) and c(gY,h) inverse factors cancel. The remaining path is (c(f,h)GZ)c(hf,gZ), giving exactly the stated Frobenius square. This is an elementary cancellation from the cited associativity identity, not an uncited pseudofunctor coherence theorem.
4. `lem-pur-derived-pullback-tensor-iso` expressly states compatibility with composition under the canonical pullback identifications. Writing this identity for the two paths in fgX = gYf and cancelling produces the displayed tensor square. I checked that its source is GX Af(M tensor N) and target Af GY M tensor Af GY N, so both sides have exactly the comparison types used by the item.
5. The same node expressly states associativity, signed commutativity and unit compatibility. The proof writes the associator, symmetry and both unitor diagrams explicitly, with the canonical unit Weil map. The symmetry is the signed derived one. No site-perfectness or flatness assumption has been added to these pullback/tensor diagrams.
6. `def-weil-weil-sheaf-complex` actually defines a Weil arrow by u theta = theta P(u). The two-line naturality calculation establishes this equation for every comparison from Steps 3-5 and every allowed Weil map. Multiplying by inverses proves the equation for inverse isomorphisms; no separate node is needed for these elementary manipulations.
7. Only clause (1) of `fix-prop-adjunctions` is used. `def-exchange-projection` gives the displayed unit--square--counit composite and its supplied-data higher-coefficient form; `def-weil-pbc-adjunction-mate` gives the identical three-factor mate. I checked s^(-1), not s, is the map LPY to PXL. `lem-pod-semilinear-field-operation-lifts` supplies the invertible canonical Ex-star comparison on these field domains. The original f is a separated finite-type morphism, but none of these nodes requires X0 or Y0 structurally separated. Frobenius is semilinear and the square is taken in schemes, with structural retagging where necessary.
8. `lem-sf-fixed-pair-adjunction-lift` states that the units and counits have exactly the original carrier components, assuming precisely this invertible-mate condition. I checked its unusual diagrammatic notation before substituting F=PY, G=PX, e=s and b=Ex-star. The expanded structures give exactly the two equations requested, on the full domains closed under all the displayed composites.
9. Clause (1) of `fix-prop-adjunctions` states both ordinary triangle equations. Clause (2) of `def-weil-weil-sheaf-complex` states faithfulness of the forgetful functor. Together they prove the lifted triangles without any exceptional adjoint or larger domain claim.

This checks delivery-errors B1-B10 and C1-C8 by keeping the sole edited node self-contained, preserving its imported metadata, using actual definition statements for the notions, recording real searches, and quoting every cited statement verbatim. D1-D5 are addressed by the explicit cancellation and naturality arguments: no new node restates a clause or receives the entire proof. Off-unit statements are declared only in `split_report.tool_uses` as generic tools, not in maintainer-owned `tool_uses`. No proof step exceeds 2000 characters, and no step hides an uncited separate comparison theorem.

For E1-E7 I tested identity f and h (the comparison equations reduce to canonical identity coherences), zero complexes (the equations remain typed), shifted one-dimensional inputs E[r], E[s] (the signed symmetry contributes exactly (-1)^(rs) on both sides), and a point with Weil map multiplication by ell. The last is an invertible rational map with no lattice on which it is an invertible integral map; the proof still works because it uses naturality in localized Hom modules. Non-separated finite-type X0 and the identity morphism are allowed: the Frobenius comparison and all generic hypotheses remain valid, with no compactification of the structural map used. I found no statement to correct; the substantive correction to the blueprint's compressed argument is the explicit direction and cancellation of the ordinary mate and coherence squares.
