# Stage-1 report: lem-sfb-flat-space-derived-external-cup

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-space-derived-external-cup.json`: item, split into ten proof steps; statement unchanged; not a Mathlib leaf.
- `citations.json`: one exact statement quotation for every step/node citation (26 entries).
- `report.md`: this report.

New DAG nodes: 0. Mathlib leaves: 0. All 17 proof dependencies already exist.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag and for external cup/Kunneth terminology. Existing scheme/field cohomology and finite-coefficient etale Kunneth declarations do not state this structure-module theorem for algebraic spaces over an arbitrary ring, with all its compatibility clauses. No project attachment claims are made.

## WANTED

None. The Stacks sources used are present locally.

## Findings and corrections

The imported item is mathematically sound and remains verbatim. It is a combined agent-stated theorem, not a single Stacks theorem: 08IN is projection formula, 08IR is Tor-independent derived base change, and 071Q is etale-Zariski equivalence. Flatness of the structure morphism, rather than flatness of the ring extension, is what permits arbitrary scalar extension. The proof now makes these roles explicit and compares the canonical morphisms by their transposes.

The inherited `blueprint.from.node` is null. The required ancestor command also returns None: the pre-existing `created.item` chain has no node with `blueprint_kind` before it terminates. I retained this mechanically computed ancestry and inherited via list, with its precise place, rather than edit someone else's node or invent an ancestor. I read the current `literature/blueprint/latest/` unit and direct-images proof, especially clause (3); the supporting alteration/Picard branch is the one already recorded by the item. The chapter and unit records were read and not altered; this item is not the unit's key node.

The Mathlib searches already on the imported item were retained. Five fresh logged searches were made with the required msearch command, including two distinct LeanFinder phrasings, Loogle, LeanSearch and source grep. The returned flat-module tensor, scheme coordinate-map, sheaf tensor and cotangent declarations do not imply this derived algebraic-space theorem. The exact query strings and actual result names are appended to `mathlib_searches`, and the tool log is `searches.jsonl`. No searches are invented or recorded as unavailable when they succeeded.

## Not duplicates

No new nodes were created. Whole-DAG searches by 08IN, 08IR, 071Q, 0FPL, 0FPM, 0H9A and external-cup/Kunneth terminology located the reused projection-formula, flat-base-change, affine realization and derived monoidal nodes. Whole-blueprint searches for Kunneth, cup product, external structure, flat cup, and coherent Kunneth found the finite-coefficient six-functor route and not another statement of the item. The field-linear group-bialgebra and underived affine relative-cup nodes are narrower consequences and are not used to infer the derived theorem. The same-source ringed Kunneth-factorizations theorem has a different domain (one q and two maps into the same X), so the distinct-space case is proved by its explicit two-counit calculation instead of an invalid application.

## Review by Q33

I read the item, the existing statements of every cited node, and the local Stacks source for 08IN (`spaces-perfect.tex`, lemma-cohomology-base-change), 08IR (lemma-compare-base-change), 071Q (lemma-derived-quasi-coherent-small-etale-site), and the full product statements and proofs in `sites-cohomology.tex`, 0FPL, 0FPM, 0FPN and 0H9A. The latter has omitted proof and a malformed left-bottom tensor expression in the source; I used its well-typed intended cup square and supplied the tensor-of-counits argument explicitly. There are no new-node sources to audit. The proof is correctly marked agent assembly because it combines those inputs with scalar normalizations, rather than claiming one source contains the whole theorem.

Step 1: Fibre-product representability comes from the stated fibre-product theorem, not from a definition of spaces. I checked that the locality node asserts base-change stability of flatness separately from properness and finite presentation; neither extra property is used. The affine-test node states arbitrary base-change stability of quasi-compactness. The diagonal and composite arguments are written in the step. The derived quasi-coherence node covers unbounded pullback and tensor, as required. The cited statements are `lem-trf-space-fibre-products-etale-covers`, `lem-sfb-space-quasicompact-affine-tests`, `lem-sfb-space-flat-proper-fp-locality`, `lem-sfb-space-derived-qcoh-pullback-tensor`.

Step 2: The affine realization node identifies the inverse equivalence with the canonical derived global sections. The scalar-sections and compositor definition nodes specify actual scalar actions, pure-tensor maps and universal derived units. I checked their statements, so the proof does not infer a normalized scalar comparison from an arbitrary equivalence. The ringed monoidal statement supplies signed tensor coherence on K-flat representatives. On an affine chart both relevant maps send the same pure tensors to the same products. The cited statements are `lem-sfb-affine-etale-derived-module-realization`, `def-sfb-space-affine-global-sections`, `def-sfb-space-affine-sections-compositors`, `lem-sfb-ringed-derived-monoidal-comparisons`.

Step 3: The cup definition states exactly the tensor-of-counits transpose used here. The abstract mates theorem supplies lax associativity and the unit diagrams; it is not cited for symmetry. Symmetry is proved separately by the equality of transposes and the symmetric comparison theorem. Thus the structure is in the ordinary derived category; no assertion of a strict commutative dg-algebra in positive characteristic is made. The cited statements are `def-sfb-ringed-site-module-cup-product`, `lem-sfb-monoidal-adjunction-mates`, `lem-sfb-ringed-derived-monoidal-comparisons`.

Step 4: The unit/counit monoidality node has precisely the hypothesis that the right lax structure is the adjunction mate; step 3 establishes that hypothesis. The ringed derived theorem states the actual composite-counit formula, including compatibility with the chosen direct-image compositor. I checked the pullback transpose, the product equation and the identity/composition formulas against those statements. The cited statements are `lem-sfb-monoidal-adjunction-unit-counit`, `lem-sfb-ringed-derived-monoidal-comparisons`.

Step 5: The projection-formula node asserts the canonical map for arbitrary unbounded quasi-coherent inputs and qcqs maps. The flat-base-change node asserts the canonical counit-mate map for a flat qcqs structure morphism and an arbitrary base morphism. Apply it to f along g, not to a possibly nonflat scalar extension. Its preservation clause makes A and C quasi-coherent. Pullback of the tensor unit is the tensor unit. I expanded the transpose of the composite: one counit on each projection is exactly the external cup transpose. This avoids citing the existing same-source Kunneth-factorizations lemma outside its own same-source hypotheses: here X and Y need not coincide. The cited statements are `lem-sfb-space-qcqs-derived-projection-formula`, `lem-sfb-flat-space-derived-pushforward-base-change`, `lem-sfb-ringed-derived-monoidal-comparisons`, `def-sfb-space-affine-sections-compositors`.

Step 6: The four-factor multiplication calculation uses the established algebra and pullback identities; the only new citation is the exact representative formula for the signed symmetry. I checked the middle interchange gives (-1)^(bc), with b the degree in the second factor of the first tensor and c in the first factor of the second tensor. Invertibility gives the equations for the inverse by composition; no extra algebra-isomorphism theorem is hidden. The cited statements are `lem-sfb-ringed-derived-monoidal-comparisons`.

Step 7: This is an elementary assembly from steps 2 through 4 and 6. I wrote the projection identities and the two-variable naturality equation explicitly, identified the triple composite, and obtained the two projection insertions by substituting the unit. No source-only assertion is used as an additional lemma. The cited statements are none; only the earlier established steps are used.

Step 8: The flat-base-change node explicitly allows arbitrary base change, preserves quasi-coherent cohomology and gives the identity/successive-base-change equations. The structural map h is flat even when B is not flat over R. The derived unit comparison is available from the monoidal theorem. The affine equivalence converts the exchange itself, not merely its cohomology groups, to the scalar comparison. The cited statements are `lem-sfb-flat-space-derived-pushforward-base-change`, `lem-sfb-ringed-derived-monoidal-comparisons`.

Step 9: The exchange/tensor node states the equality for projection maps and the canonical mate, without any base-change invertibility requirement. Mate pasting states the specified equality of pasted mates. The derived monoidal node makes composition and ringed commutation comparisons monoidal, hence theta has the needed tensor compatibility. I wrote the counit-mate equation and its tensor with a second copy: both cup-square transposes are the same. The unit case is its tensor-unit instance. Pasting then supplies pullback and external-cup compatibility. This is the argument omitted by Stacks 0H9A, written here using cited existing generic results. The cited statements are `lem-weil-pbc-ringed-exchange-tensor-coherence`, `lem-weil-pbc-mate-pasting`, `lem-sfb-ringed-derived-monoidal-comparisons`.

Step 10: The etale-Zariski nodes identify the structure module, canonical derived global sections and pullback/direct-image comparisons. The monoidal theorem applies to the topology-change ringed morphism and identifies the composite adjunction counits. I checked that comparing the two cup transposes proves equality of the actual products, rather than an unspecified graded-ring isomorphism. All inputs here are quasi-coherent, as required by the equivalences. The cited statements are `lem-sfb-derived-etale-zariski-equivalence`, `lem-sfb-scheme-derived-etale-qcoh-comparison`, `lem-sfb-ringed-derived-monoidal-comparisons`.

I checked delivery-errors B-E point by point: no new statement-only nodes are needed, no proof is hidden in a new statement, no clause is relabelled, all citations use the cited statement rather than its proof, all hypotheses in the two geometric isomorphism results hold, and all proof dependencies are the union of step uses. The actual citation quotations were checked as literal substrings of the existing statements. I checked all reused dependencies transitively for a cycle back to this item: none. Generic off-unit adjunction, tensor and fibre-product tools are declared in split_report.tool_uses; they do not replace the unit's route.

Edge checks: an empty factor gives the zero derived algebra and the zero external product on both sides; X=T or Y=T gives precisely the unitor and the claimed projection unit insertion. For affine X=Spec A and Y=Spec C, the comparison is A tensor-derived C to A tensor C, an isomorphism since the relevant algebras are R-flat; the pure-tensor product has the stated sign. Nonflat extensions such as Z to Z/2 are covered by structural flatness; the argument never treats ordinary scalar extension as exact. Nonprojective cohomology is allowed throughout. Multiple scalar extensions use the canonical derived tensor associator and counit mates, not arbitrary identifications. Derived commutativity uses the Koszul symmetry, so no division by 2 and no claim of strict commutative resolutions is present. No Noetherian, finite-type or properness hypothesis is introduced.

Every step has length below 2,000 characters (maximum 1,212). I reviewed the comparison calculations for hidden standalone lemmas: each is an explicit application or a short equality of transposes using existing nodes. No new unproved mathematical fact is smuggled into a long step. No repository file or launcher file was written, no git command was run, no Lean was written, and no compiler/Lake/build tool was run.

## Unfinished work

None in the split. The server dry run and direct push follow this report; their result is recorded below once completed.

## Validation

The required `deliver.py Q33 lem-sfb-flat-space-derived-external-cup --no-push` exited 0 and printed `OK (not pushed)` at `b07d86b6614`: server preflight passed, including DAG and split review. The direct delivery follows this successful completed dry run. Zero new DAG nodes; zero Mathlib leaves.
