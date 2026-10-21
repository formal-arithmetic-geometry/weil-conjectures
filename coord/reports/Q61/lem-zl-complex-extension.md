## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-complex-extension.json`: split statement; no Mathlib match. Five proof steps, using existing nodes only.
- `citations.json`: twelve verbatim statement quotations, one for each node cited in each proof step.
- `searches.jsonl`: five actual msearch invocations, retained without alteration. `prepare.py` and `bbd.txt` are sandbox research artifacts, not delivery files.

New nodes: 0. New Mathlib leaves: 0. The item is not the unit's key definition, so no unit realization record is changed.

## Attachments

None. `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.of_distTriang`, `lean/WeilConjectures/DeligneLaumon/Reduction/Weights.lean:377`, has no `sorry` in its own proof, but its `WeilComplex` is a bounded constructible subcategory of the derived category of pro-etale Weil sheaves (`WeilSheaf/Category.lean:169-194`). The actual DAG definition is the fixed-pair category over the common-stage derived category and explicitly distinguishes the two categories. Thus the tagged theorem does not give an exact attachment for this item. No claim of transitive Lean closure is made.

## WANTED

WANTED: `weil_conjectures_complete_notes.pdf`, section 12.2, Lemmas 12.2-12.5, the unavailable notes named by this chapter, for lem-zl-complex-extension. This is already listed as wanted in `literature/LIST.md`. The delivered proof is marked agent-written and follows the available blueprint proof with the category repair described below.

## What was wrong

STATEMENT-DISPUTED: the imported phrase "a distinguished triangle in the constructible Qbar-Weil categories" is ill-typed against the current `def-weil-weil-sheaf-complex`: its last paragraph explicitly supplies no triangulated structure. It is a category of pairs in the underlying derived category. The live upstream declaration uses a different derived category and cannot silently repair this discrepancy.

The obstruction is visible on a point. In the fixed-pair category over the geometric point, Hom((Qbar,1),(Qbar[1],1)) is zero, whereas the nonsplit two-dimensional unipotent Jordan Frobenius representation is an extension of the trivial representation by itself in the Weil heart. Its underlying short exact sequence is split as vector spaces and gives a distinguished triangle in the underlying derived category with zero connecting arrow. Declaring all such underlying distinguished diagrams distinguished in a triangulated category of pairs would force this zero-connecting-arrow triangle to split equivariantly, contradicting the Jordan block. Thus there is a real categorical distinction, not merely missing notation.

The repaired statement specifies two commuting arrows of Weil pairs and requires that their underlying arrows extend to a distinguished triangle in the actual common-stage coefficient category. This expresses precisely the part of the intended hypothesis used by the source proof, without claiming a triangulation of pairs. It also works when the underlying connecting arrow has not been equipped with equivariance; the argument uses only exactness at the middle cohomology sheaf. All field, scheme, coefficient, embedding and weight hypotheses are explicit. The conclusion is unchanged.

The old long-exact citation applied a theorem about homological functors without supplying that property for the actual cohomology functor. The proof now cites the standard t-structure at the actual common-stage category and the generic t-structure cohomological-functor theorem. The old bare cohomology-sheaf definition did not alone establish exactness. Frobenius-module lemmas mentioned only as a stalkwise shadow have been removed from proof dependencies: sheaf stability already supplies the needed assertion, and punctual stalk bounds alone would not be a replacement for the global mixed filtration.

## What could not be finished

Nothing remains in the stage-1 split. No Lean was written, compiled, or built. No repository, launcher file, source definition or target statement was edited. The independent maintainer review remains part of the normal delivery process.

## Not duplicates

No new nodes. Searches of the whole DAG and imported blueprint for complex weights, long exact sequences, homological functors, fixed pairs and Serre classes located the existing nodes now used. The neighboring retract lemma does not assert extension stability. No elementary image factorization or sheaf clause of the item was promoted to a node.

## Review by Q61

I read both the original master statement/proof and the current main-20261015 statement and separate proof file, the chapter record and the unit record. Both snapshots give the same degreewise long-exact/image/quotient argument; the unit defines mixedness by filtrations and records subobject, quotient and extension closure. I kept that route. I read the entire current statements of every cited node, including the refined fixed-pair definition, the weight definition with its induced cohomology Weil action, and the existing sheaf-closure lemma. I also read that lemma's current blueprint proof. There are no new-node sources to check. As an external cross-check of the generic tool in step 1, I read BBD, Faisceaux pervers, Theorem 1.3.6 and its proof on printed pages 31-32: the heart is abelian and H^0 is cohomological. This use concerns general t-structures and does not invoke an SGA route. For step 3 I read Stacks 010N, homology-lemma-exact-functor, in homology.tex, and the stronger explicitly stated kernel/image/quotient compatibility in the existing DAG lemma. No SGA source is cited or used.

Step 1 uses `prop-constructible-truncations` for the bounded standard t-structure on precisely the rational/common-stage coefficient category, and clause (5) of `lem-weil-heart-short-exact-triangles` for the cohomology exact sequence. Its hypotheses are satisfied by the underlying distinguished triangle, not by an invented triangle in the pair category. `def-weil-complex-weights` identifies these as the actual cohomology sheaves used by the weight predicate. The finite-type geometric scheme and coefficient field are those in the truncation statement.

Step 2 uses the natural automorphism/cohomology comparison of `prop-constructible-truncations`, the commuting-square definition in `def-weil-weil-sheaf-complex`, and the literal cohomology Weil-action formula of `def-weil-complex-weights`. I wrote the naturality equation rather than saying merely that the Weil structures transport. Substituting u and v proves both induced arrows are Weil arrows. No connecting-arrow naturality is needed.

Step 3 uses the exact-heart restriction asserted by `lem-a1-constructible-pullback-t-exact`, specialized to geometric Frobenius (an automorphism between the same finite-type geometric scheme). Parts (a),(b) of `lem-sp-exact-functor-preserves-homology` explicitly supply quotient and image comparisons compatible with their canonical maps; this is not an appeal to the definition of exactness for an unstated theorem. The abelian Weil-heart setting is explicitly in `lem-a1-mixed-direct-summand`. I wrote the induced image action, its inverse, quotient action, and the descent equation after the epimorphic quotient map. Exactness gives ker(g)=I, so B/I embeds in C. The remaining kernel/cokernel universal-property check is elementary and written out: unique factorizations commute with Frobenius after a mono/epi cancellation. This is an elementary application of the cited comparisons to the two arrows, not a hidden weight lemma or a new global comparison theorem.

Step 4 uses exactly clauses (1) and (2) of `lem-a1-mixed-direct-summand`. Clause (1) applies to the quotient of A and the subobject of C, and clause (2) applies to the resulting short exact extension of constructible Weil sheaves. Both outer bounds are w+j, obtained from `def-weil-complex-weights`; there is no incorrect shift or semisimplicity assumption. Step 5 is the universal quantifier in that same weight definition. The twelve quotations in citations.json were verified by literal substring inclusion in the current dependency statements; they are not paraphrases.

I tested the statement on zero complexes and the empty scheme, on the identity/split triangle, and on the unipotent Jordan extension on a point. Zero images or quotients cause no exception, and mixed filtrations permit zero successive quotients. In the Jordan example, the subquotient-and-extension argument works without asserting an equivariant splitting; it is also the explicit test that rules out the imported categorical formulation. Negative degrees and arbitrary real bounds use the identical w+j convention; boundedness is inherited from the objects, not an extra exactness hypothesis.

For B-E of delivery-errors: no new statements, duplicate nodes or unrun search records are introduced; all concepts use the existing categories; all five search results were read, including the general Serre-class lemma `CategoryTheory.ObjectProperty.prop_X₂_of_exact` at Mathlib/CategoryTheory/Abelian/SerreClass/Basic.lean:65. That generic lemma requires a Serre predicate and does not establish the actual Weil-pair coefficient model or its mixed predicate, so the item is not a one-line Mathlib specialization. The five proof steps have lengths 666, 665, 1385, 542 and 219 characters; none exceeds 2000. The elementary image construction remains a step, as required by the no-elementary-node rule. I checked that none of the newly cited existing dependencies has a dependency path back to this item. The four generic off-unit tools and their exact roles are declared in split_report.tool_uses; sheaf-level weight stability remains in this unit. No chapter or unit route is changed.

## Server validation

The standalone server review_split passed with zero new nodes. The first delivery dry run reached full preflight, but check_dag could not establish its baseline because the server returned Errno 28 (No space left on device) while creating its temporary baseline tree. No mathematical or structural failure was reported and nothing was pushed. The citation excerpts were subsequently made step-specific (t-structure for step 1, cohomology Weil action for steps 1-2, and abelian-heart/image/quotient statements for step 3); all twelve remain literal quotations. A final dry run is required after that change.
