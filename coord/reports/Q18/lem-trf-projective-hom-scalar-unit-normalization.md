## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-projective-hom-scalar-unit-normalization.json`: item, statement, split; Mathlib searches find ingredients but no match for the complete derived normalization.
- `citations.json`: one verbatim statement quotation for each of the 13 step/cited-node pairs.
- `searches.jsonl`: six actual searches from the required launcher command, including a second semantic phrasing and a targeted grep.
- `report.md`: this report and direct-delivery review.

No new nodes and no Mathlib leaves. The item's original statement, statement dependencies, creation provenance, and existing search records are retained. Only its proof, proof dependencies, proof origin, split status, split report, and appended search evidence are supplied. Each proof step is shorter than 2000 characters.

## Attachments

None. Searches under the live `lean/WeilConjectures/` for the exact blueprint tag return no match. Concept searches found ordinary scalar-Hom formulas and flat Ext material, not a declaration giving all the item's derived internal-Hom, unit normalization, unbounded-target and arbitrary-morphism clauses. In particular `rawModuleScalarHom_evaluate` and `rawModuleScalar_hom_composite_formula` concern maps of raw étale Hom groups with source/coefficient factors, rather than this map of module-derived internal-Hom objects. `ExtFlatBaseChange.lean` concerns Ext-group closure properties. No attachment is claimed and no compiler was run.

## Literature wanted

None. All the source text needed here is available in `literature/stacks-project/more-algebra.tex`.

## Corrections and scope

The imported item had no proof. No statement dispute or source error was found. The proof is an agent elaboration of Stacks Tag 0E1W, label `lemma-upgrade-adjoint-tensor-RHom`, and Equation 0E1X, label `equation-base-change-RHom`: I read both, including their actual unit/precomposition formulas. The auxiliary projective-source input is Tag 0A66, label `lemma-RHom-out-of-projective`; the scalar derived adjunction is Tag 0GMT, label `lemma-tensor-hom-adjoint`. I also read the product-Hom differential, Tag 0A5Y `lemma-compose`, Tag 0GWQ `remark-internal-hom`, and the derived internal-Hom characterization `equation-internal-hom` in the same file. No SGA source is used.

The latest blueprint's `sec-trace-formula/_section.md`, `sk-i-curve-zero/_section.md`, and `lem-trf-local-term-locality.proof.md` were read. This is the inherited algebraic tool in that ancestor's nearby-cycle/relative-duality branch, not a replacement of the unit's contracting-correspondence argument. The chapter and unit records are not modified. Whole-blueprint searches for `scalar adjunction`, `projective Hom`, and `base-change-RHom` found no blueprint statement equal to this normalization; `blueprint.same_as` stays empty. `blueprint_refs.py ancestor` confirms `lem-trf-local-term-locality`.

## Mathlib searches

I read all six results produced by `msearch.py`, including the second LeanFinder phrasing. All services answered successfully. The first phrasing gave projective Ext and ordinary module extension/restriction; the second gave ordinary monoidal-closed evaluation and ordinary scalar extension. Loogle on `"HomComplex", "Adjunction"` returned zero hits. The broad grep was noisy because the command is case-insensitive; the second grep restricted to `Algebra` isolated ordinary change-of-rings formulas. LeanSearch found `CategoryTheory.Adjunction.derived_unit` and ordinary scalar transposes. I opened `ModuleCat/ChangeOfRings.lean` around lines 700--790, `TensorProduct/Tower.lean` around lines 690--740, and the generic derived-adjunction file. Ordinary scalar adjunction and `LinearMap.baseChangeHom` do not identify an internal-Hom chain comparison with the specified localized unit transpose. The generic derived-unit identity supplies no such Hom model or evaluation identification. These are ingredients, not an exact match or a one-line specialization of the item. The new records use exactly the tool/query texts logged in `searches.jsonl`; yesterday's embedded search records are preserved.

## Not duplicates

There are no new nodes, hence no new/existing same-tag pairs. The relevant existing statements are reused: `lem-trf-flat-projective-hom-models` for the flat models and scalar unit/counit; `lem-pod-projective-hom-evaluation-model` for derived evaluation with its actual sign; `lem-sfb-dc-hom-scalar-adjunction` for uniqueness and naturality of the evaluation-normalized internal-Hom scalar isomorphism; and `lem-pc-normalized-ring-hom-extension` for the already constructed chain map. None of these alone identifies the unit transpose with that chain map. The item's argument supplies that identification directly, rather than creating another node for the item or one of its clauses. I checked the candidate dependencies' statement/proof closure: none depends on this item, so these citations introduce no cycle.

## Unfinished work

No mathematical step of this item is deferred. The existing cited lemmas retain their current project statuses; this is a one-level stage-1 split, not a claim that their Lean proofs are finished. No Lean files were written, no builds or compilers were invoked, and the shared repository and launcher files were only read.

## Review by Q18

I reread the item, the seven cited node statements, the Stacks source passages above, and the latest blueprint with the completed proof open. Here is the substantive check against delivery-errors B--E.

Step 1 uses exactly the singleton-site module comparison and the flat projective-Hom models. The former states the equivalence and the scalar unit, including localization; the latter states the flat functor's comparison on every complex, projectivity of the extended source, the two derived Hom models, the same model with target U(FN), and both scalar unit/counit formulas. Flatness is used here, and bounded-above projectivity is imposed on P alone. This avoids incorrectly assuming H or N is bounded or K-flat. Tensor symmetry changes the source's right-tensor convention and its unit to the displayed left-tensor convention by its explicit formula.

Step 2 uses only `def-sc-module-total-hom-complex` for the product and its differential. The argument explicitly constructs both directions, checks balancing and their inverse identities on tensor generators, and writes the common differential coordinate. Product extensionality and tensor generation suffice; there is no assertion that scalar extension commutes with an infinite product. This is elementary algebra from the cited definition, not an uncited scalar-comparison theorem.

Step 3 uses `lem-pod-projective-hom-evaluation-model` over R and S, `lem-trf-flat-projective-hom-models`, and `lem-sfb-dc-hom-scalar-adjunction`. I checked their statements: the evaluation-model lemma includes the derived counit and its sign, the flat-model statement includes the comparison/unit normalization, and the scalar-Hom statement says the isomorphism is uniquely determined by exactly this evaluation equation. I checked the tensor identification by writing its inverse as well as its forward map, then the evaluation equation gives the same sign (-1)^(pn) on both sides. Thus a does represent the prescribed derived scalar-Hom adjunction, not an arbitrary natural isomorphism or merely a cohomology-group isomorphism. This is the non-elementary comparison step, and its imported ingredients all have cited nodes.

Step 4 uses the same flat-model statement for the unit and natural projective-source model and the total-Hom definition for target functoriality. It writes Hom applied to that chain unit and then the inverse of a. The displayed formula is valid for any homogeneous family, not just a degree-zero cycle. This is substitution and the differential calculation, so elementary relative to those statements.

Step 5 uses the flat-model statement for the actual derived scalar adjunction, including its counit, and the existing normalized chain-map statement for the formula of chi. The mate is written as the composite of scalar extension and the counit; evaluating on s tensor f and t tensor x gives st tensor f(x). Generation and product extensionality identify the chain maps. The final comparison is written with all three model isomorphisms in the correct order, from LF(RHom) through Q_S(FH) to RHom_S. No new lemma is being substituted for the desired equality.

Step 6 uses the derived-Hom definition for its bifunctor on the whole derived category, the scalar-Hom lemma for naturality in both derived inputs, and the flat-model statement for compatibility with localization and changing representatives. The naturality equation is for an arbitrary morphism of D(R)^op times D(R); multiplying its equation by inverses proves the inverse-morphism case. Thus it does not assume every derived morphism has a chosen chain representative. The only new reasoning is naturality of a composite/adjoint and cancellation, which is elementary once these cited functors and transformations are given.

For E1--E4 I checked the hypotheses where used: the singleton site is small, the rings are commutative, the map is flat, P is bounded above with projective terms, and FN need not be bounded. FP has the required projective terms by the cited model theorem. For E5 the actual tensor formula, the inverse tensor identification and the evaluation equation are all written, so no appeal to an unspecified transport remains. For B/D there is no new node that could be elementary, duplicate, a clause restatement, ill-defined, or missing a definition/source. All inherited statement dependencies are retained, and every non-elementary input in the proof is among the explicitly cited statements; the 13 verbatim quotations were checked against those statements. The off-unit generic tools are declared in `split_report.tool_uses`, without editing the maintainer's `tool_uses` field.

I tested the formulas at P=0, N=0, S=0 (when the zero ring is allowed), and R=S with identity map: they give zero maps or the identity comparison as appropriate. For P and N concentrated in degree zero they reduce to the ordinary tensor-Hom adjunction. With odd source and Hom degrees the two evaluation sides both acquire the same minus sign, which is why omitting the Koszul check would have been unsafe. For an infinite-rank projective source or an unbounded target, the proof still uses only product coordinates and tensor generators, never surjectivity/invertibility of chi. There is no finite-generation or perfectness assumption hidden in the argument.

The correction made during this self-review was to make the tensor identification in step 3 explicitly invertible by a balanced inverse, rather than leaving its normalization implicit. No other statement or route correction was needed.
