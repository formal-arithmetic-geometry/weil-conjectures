# Q51 stage-1 delivery

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-common-stage-restriction-tensor-descent.json: item, statement; eight-step split, statement unchanged. Not a Mathlib leaf.
- No new nodes and no Mathlib leaves.
- citations.json: one verbatim quotation for every step/node citation.
- searches.jsonl: actual Q51 search command log; the item's preexisting Q126 search history is retained in the item.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag, common-stage terminology, and restriction/tensor combinations. Existing FieldCoefficient modules, scalar-extension tensor maps, and filtered-two-colimit code do not state this item's complete common-stage restriction comparison with its specified representatives, units, and mixed squares. No compiler or Lean-writing tool was run.

## WANTED

None. The missing argument is written by the agent from the explicit hypotheses and existing categorical prescriptions, not attributed to an unavailable reference.

## Findings and changes

The live item was unsplit and the sandbox held no prior item or report. I copied the live item and retained its statement, source, blueprint ancestry, creation data and previous searches. There is no released repair note. The current blueprint source, literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md, asserts invertibility but does not give this coefficient-descent calculation. The proof is therefore explicitly agent-written. It realizes the existing subargument under the finite-clopen decomposition and finite-product field coefficient descent, with no alteration of the chapter or unit route.

The substantive calculation now distinguishes the actual source/target objects from their scalar-extended models. Step 4 displays p and q; step 5 proves q S(c_H) = c_K p from the mixed square and scalar towers. Step 6 writes the conjugated arrow formula and the naturality equality, and step 7 writes the unit endpoint comparison. Thus none of the assertions depends on treating different-stage objects as literally equal.

## Not duplicates

No new nodes. Searches of the whole DAG and blueprint included common-stage, tensor, scalar, restriction/descent, and the specific common-stage comparison nodes. The broader pair-functor descent lemma lem-sbc-coherent-pair-functor-descent has additive functor families; the tensor bifunctor is bilinear and is not additive as a functor from the product additive category. I therefore did not invoke that lemma on an inapplicable product category. The framework common-stage descent and PBC common-stage calculus were also read, but do not replace the mixed tensor calculation required here. No restatement of an item clause was made into a new node. Every remaining step is either an invocation of an existing stated comparison or a displayed substitution/cancellation from the item's hypotheses and definitions.

## Mathlib search assessment

All Q51 queries in the item were run through batch2/msearch.py and their actual records copied from searches.jsonl. Two semantic phrasings were tried. LeanSearch returned ordinary tensor base-change equivalences; Loogle returned NatTrans.IsMonoidal and its elementary closure instances; LeanFinder returned finite filtered diagram lemmas, ordinary monoid colimits, and Day convolution comparisons. The grep in CategoryTheory and the targeted grep in CategoryTheory/Monoidal/NaturalTransformation.lean do not supply raw common-stage coefficient descent. I read the monoidal-natural-transformation definition and closure instances in the Mathlib source, as well as tensor tower code. These are not an exact statement or one-line specialization: the prescribed coefficient-category representatives and endpoint conjugations still need the calculation written here. No unavailable service was recorded as a negative result.

## Review by Q51

I read the current blueprint section-invariant source and the chapter/unit records. For this item's proof I also opened the complete statements of def-weil-derived-pullback-tensor-hom, def-weil-algebraically-closed-coefficients, lem-pur-integral-operations-scalar-extension, lem-weil-scalar-extension-composition, def-weil-finite-subextension-directed-set, and lem-weil-constant-coefficient-objects-constructible. There are no new-node sources to audit.

Step 1 uses the operations definition's actual object and arrow prescriptions, the integral operations comparison's stated naturality and identity/tower compatibility, and the scalar composition node's canonical associators. The morphism direction is f:Y→X, so r maps the X category to the Y category, as every subsequent formula requires. These statements are used only as given comparison tools; the proof does not infer an unstated monoidal structure from a definition.

Step 2 uses the finite-subextension statement for the finite compositum, the operations definition for the source (H,D_H) and target (H,Q_H), and the pair-category composition rule to turn the explicit inverse at H into an inverse class. The source of d_H is Q_H and its target is r_H M_H tensor r_H N_H; hence d_H^{-1} mu_H has precisely the item's required direction.

Step 3 cites no node because it merely left-multiplies the assumed mixed square by the inverse of b_U tensor b_V. I checked both endpoints of the resulting formula. Step 4 uses exactly the stated scalar tower comparisons to define p, q, x_M, y_M and to give the two tower equations. All terms stay in the K category; p starts at S^Y D_H and q starts at S^Y Q_H. Step 5 uses the comparison lemma's naturality of theta, substitutes step 3, cancels using the two tower equations, and invokes the hypothesis of naturality of mu_K. This gives the displayed equality, not just an assertion that transport works. Directedness and the pair-category equality criterion then handle incomparable common fields. The same conjugation of inverses follows by multiplying by p^{-1}, q^{-1}.

Step 6 uses directedness to place arbitrary representatives at one L. Its formula w=d_L'^{-1}(r_Lu tensor r_Lv)d_L is exactly the pullback-arrow conjugation in the operations definition, applied in each factor. The equality w c_L=c_L' r_L(u tensor v) follows by cancelling d_L and applying naturality of mu_L. Restoring the displayed p and q reinstates the theta conjugations of the tensor-arrow prescription, so this checks actual common-stage arrows. Eventual equality of representatives is exactly the cited pair-category statement. No faithful scalar-extension or lifting of arbitrary arrows to their original fields is assumed.

Step 7 uses only the constant-object node's explicit unit scalar isomorphism, together with the mixed unit square assumed in the item. Its two endpoints p_1 and q_1 make the equation q_1 S(epsilon_E)=epsilon_L p_1 type correctly. The inverse equation follows by cancellation. Step 8 uses finite composita, the actual operation formulas, and common-field composition to conjugate each specified finite equation by its external endpoint maps. It asserts preservation only of equations already satisfied by the finite-stage data; it does not introduce associativity or unit laws as new hypotheses or prove unspecified laws by fiat.

I checked B through E of delivery-errors.md against these files: quotations are verbatim from statements; no cited proof internals, hidden source lemmas, new hollow definitions, duplicate nodes, or changes to target statements occur. No node was introduced for elementary algebra. All proof steps are shorter than 2000 characters. Small cases checked were E=F, K=H, f the identity, identity input arrows, zero objects, an empty scheme, and two nonnested representative fields. They require only the same unit comparisons, inverse cancellations and finite compositum; none calls for idempotent completion, an unmentioned separateness hypothesis, or full faithfulness. The only correction during drafting was to keep explicit p and q instead of suppressing field-change identifications.

The three comparison statements from other units are declared in split_report.tool_uses: they supply the given scalar-operation, scalar-tower and coefficient-unit tools, rather than replacing the unit's proof route.

## Unfinished work

None in the stage-1 split. Server dry-run and delivery results are recorded after running the required delivery tool.

## Validation

The required deliver.py --no-push invocation exited 0 and printed OK (not pushed) at a1c9517f7c6: preflight passed. The server checks accepted the DAG, split, logged searches and verbatim citation record. No overlapping delivery invocation was started.
