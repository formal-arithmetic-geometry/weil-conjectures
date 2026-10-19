## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometrically-reduced-base-change.json`: item split into five steps; statement and statement dependencies unchanged. Not a Mathlib leaf.
- `citations.json`: verbatim statement quotations for all eight step/node citation pairs.
- No new nodes or unit changes. `searches.jsonl` contains the five actual Mathlib searches from this attempt.

## Attachments

None for the item. The project declaration `isReduced_tensorProduct_of_forall_residueField` in `WeilConjectures/Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean:47` is sorry-free in its displayed proof but has the different hypothesis of reduced tensor products with residue fields of R, rather than the item's all-field-extensions hypothesis on A. The perfect-field tensor theorem at line 123 adds perfectness. Neither is reported as an exact attachment. Searching WeilConjectures for the item id and the geometric-reducedness/tensor notions found no exact declaration of the item. The already attached `Algebra.tensor_finite_type_limit` belongs to `lem-weil-pbc-tensor-finite-type-limit`; it was read as a related existing input, but the item instead writes the one-factor finite-support argument directly.

## WANTED

None. The entire proof is in the local Stacks source.

## Errors found and changes

The item is correct as imported. I read Stacks `algebra.tex`, Tag 034N, `lemma-geometrically-reduced-any-reduced-base-change`, lines 10129–10151, together with the preceding Tag 00I3 finite-expression argument. The hypotheses are precisely a field k, an algebra A whose tensor with every extension field is reduced, and an arbitrary reduced k-algebra R. In particular neither finite type nor nonzero was added to the statement. The proof was empty and is now explicit.

The source compresses the tensor injectivity and finite-product distribution arguments. I supplied their details using existing statements. Only finitely generated subalgebras of R are introduced; A is kept fixed throughout. This avoids needing an unproved assertion that an arbitrary finitely generated subalgebra of A has some alternate geometric-reducedness predicate. The map that inserts one factor into a finite product is used only as a linear map, because it is generally not a unital ring homomorphism. No infinite-product/tensor interchange is asserted.

Blueprint searches `blueprint_refs.py search '034N'` and `search 'geometrically reduced any reduced base change'` returned no blueprint equivalent. DAG searches for 034N, the label, tensor reducedness and finite products of fields found the existing total-quotient decomposition, field-module flatness, flat tensor exactness and finite-type Noetherian leaf, all reused. No new nodes need a `Not duplicates` pair. The inherited blueprint ancestor and via chain are retained. The imported unit is `sk-i-curve-zero`; this algebraic input serves the existing separable-constants-extension chain below its local-term node, and changes none of its geometric steps.

The five searches run with msearch were LeanFinder (two distinct natural-language phrasings), Loogle, grep in RingTheory, and LeanSearch. All services returned successfully. I read the candidates in Mathlib `RingTheory/Nilpotent/GeometricallyReduced.lean`, including the TODO at lines 35–37: its typeclass uses the algebraic closure, and its available field-extension tensor instance assumes algebraicity. `IsReduced.tensorProduct_of_flat_of_forall_fg` at `RingTheory/Flat/Basic.lean:642–658` is only the finite-subalgebra reduction criterion. These are not exact matches or one-line specializations of this item. Existing search records were retained, and the actual current log records were appended without inventing or changing queries.

## Unfinished work

No mathematical part of this one-level split is left unfinished. Existing dependencies retain their own states. No Lean was written or compiled and no shared file or launcher was changed.

## Review by Q36

I checked the unchanged statement against Tag 034N, label `lemma-geometrically-reduced-any-reduced-base-change`, in the local `algebra.tex`. Its definition of geometric reducedness is the all-extension-fields condition already written out in the item. I also read the source's cited product-of-fields argument: 00EU (`lemma-minimal-prime-reduced-ring`), 00EW (`lemma-reduced-ring-sub-product-fields`), 00FR (`lemma-Noetherian-irreducible-components`), and 02LX (`lemma-total-ring-fractions-no-embedded-points`). The sandbox adds no child statements, so there are no new-node source or hypothesis checks to defer.

Step 1 cites the actual statements of `lem-weil-pbc-module-over-field-flat` and `lem-weil-pbc-flat-tensor-exact`: the former applies to A as a vector space over k, and the latter explicitly preserves the initial zero in an injective exact sequence. Thus it supplies the needed injection, rather than merely defining flatness. The ring-map verification on pure tensors is written out. A=0 is allowed by both statements.

Step 2 cites the first conclusion of `lem-wf-affine-noetherian-components`, which says a finitely generated algebra over a field is Noetherian, not merely that its spectrum is Noetherian. Reducedness of B follows from its inclusion in the given reduced R. These are exactly the hypotheses of `lem-weil-pbc-reduced-noetherian-total-ring-fractions`, whose statement supplies both the fields B_q and their finite product decomposition of Q(B). I opened that node and did not take its proof as an extra statement. It does not explicitly claim injectivity of B→Q(B), so the step proves it with the zero criterion in `def-weil-pbc-module-localization` and the definition of a nonzerodivisor. Composing the resulting embedding with the canonical product isomorphism is k-linear; each factor is nonzero and hence really is an extension field of k. The B=0 case is discharged explicitly. I declared the decomposition node as a generic off-unit tool in split_report, because it is exactly the source's commutative-algebra input and replaces no trace-formula unit step.

Step 3 uses the universal property and generation clauses of `def-weil-pbc-module-tensor-product`. Its maps are stated explicitly. Projections followed by coordinate insertions give the Kronecker identities, and the finite sum of coordinate projections is the identity, so the maps are inverse on pure tensors and hence on all elements. Multiplication is checked by the pure-tensor formula. This is an elementary finite direct-sum calculation, not a hidden geometric lemma or a new node. The nonunital coordinate maps are never falsely used as algebra homomorphisms.

Step 4 uses exactly the all-field-extensions hypothesis for each K_i from step 2. It writes the swap isomorphism, tests nilpotence coordinatewise in the finite product, and uses the injection from step 1 to descend reducedness. Its only new calculation is elementary, given the previous steps; the tensor-definition citation really states the universal property and the generation clause used by the swap. It does not invoke the unavailable equivalence between the Mathlib algebraic-closure predicate and the Stacks predicate.

Step 5 again uses the generation clause of the tensor-definition statement to write a finite sum, absorbing scalars into r_j. The generated subalgebra is finitely generated by construction. The injection already established in step 1 is what shows that z_B^n=0, rather than inferring nilpotence from an arbitrary noninjective map. Step 4 then kills z_B. This is the expanded first sentence of the source proof, with all finite-support and zero arguments present.

For B–E of delivery-errors: there are no new statement-only nodes to violate B1–B3, all formulas use single-escaped TeX in the JSON, sources name tags and labels, and the item has its blueprint reference and a split_report. Every non-elementary fact is in a cited statement, verified by opening it; citations.json quotes these statements verbatim. None of the cited nodes depends back on this item. No clause has been moved wholesale into a new node. All proof steps are below 2000 characters, and the finite-product comparison is a short explicitly inverted routine map, not a hidden lemma.

I tested the argument on R=0, A=0, R=k, A=k, R=k[x,y]/(xy), and finite products of fields. It also applies when R has infinitely many generators, since each individual tensor has finite support. To test the necessity of the geometric hypothesis in characteristic p, take k=F_p(t) and R=A=k(t^(1/p)); A is reduced but fails the item's hypothesis, and the difference of the two copies of t^(1/p) is a nonzero nilpotent in R⊗_kA. Nothing in the split incorrectly admits that example. No hypothesis about perfectness, algebraicity, finite dimensionality or reduced base-change schemes is used. This is ordinary commutative algebra; no coefficient-category or canonical sheaf base-change morphism is involved, no target statement changes, and no SGA source is cited.
