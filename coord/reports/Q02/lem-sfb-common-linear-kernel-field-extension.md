# Stage-1 report: lem-sfb-common-linear-kernel-field-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-common-linear-kernel-field-extension.json`: statement, now split into five steps; no exact Mathlib match. Statement and statement dependencies unchanged. Existing searches retained and five searches from this run appended from their actual log records.
- `citations.json`: one verbatim statement quote for every proof-step citation (four citations).
- `report.md`: this report.

No new nodes, no new Mathlib leaves, no Lean files, no unit edits.

## Attachments

None. Searched the live `lean/WeilConjectures/` both for the exact blueprint id and for common kernels, kernel/base-change combinations, simultaneous equations, and tensor-basis arguments. The finite-coordinate theorem in `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` assumes finite dimension and has a different conclusion. `TensorProduct.eq_zero_of_forall_rTensor_eq_zero` in the project's `Mathlib/LinearAlgebra/TensorProduct/Basis.lean:32-48` is a genuine sorry-free family-detection theorem, already represented by `lem-sfb-vector-space-tensor-family-zero-detection`; it addresses a zero common kernel and does not itself state this item's arbitrary-kernel identity. Neither is an attachment for this item.

## WANTED

None. The Stacks sources needed for this proof are present locally.

## Corrections and route

The item was statement-only and had no proof. Its statement is correct, including arbitrary dimensions and empty E, and has not been changed. Its source already called it an agent coefficient-basis consequence; the proof now supplies exactly that argument. Source/proof metadata explicitly names Tag 09FN for basis existence and Tag 00CX for tensor generation and bilinearity. The contextual Mittag-Leffler references 059R and 059M do not supply any uncited black box in this proof: no tensor/product comparison or preservation of infinite limits is asserted or used.

Read the chapter record, the unit record, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. This is a lower-level linear algebra input on the existing alteration/descent route under direct images, not a replacement for any unit step. There is an inherited metadata mismatch: `dag/units/sk-thm-sf-ctf-stability.json` is filed as chapter `sec-six-functors`, whereas the item's chapter and the current blueprint unit are `sec-six-functors-basics`. No chapter or unit record was changed. `blueprint_refs.py ancestor` returns `None` for this inherited created-item chain. The item's existing `from.node: null`, detailed `from.place`, and `via` list are retained; the report binds the proof to the exact current blueprint place. No statement dispute or change to a target is involved.

## Searches and reuse

No item node, proof, report, or search log existed in this sandbox at start. Read the current repository item's seven historical search records and preserved them. New searches were made only through the prescribed msearch command, with group Q02 and this item id; all five results were available and are retained as returned in `searches.jsonl` and copied into the item's records with exact tool/query text.

The first semantic query asks about arbitrary common kernels under field extension; the second asks about scalar extension and arbitrary intersections. Also ran LeanSearch, Loogle `"baseChange", "ker"`, and the logged grep for iInf/baseChange, ker/baseChange and right-basis coordinates. Read the actual search types and the Mathlib source at `TensorProduct/Basis.lean:88-101`, `TensorProduct/Tower.lean:899-902`, and `Dual/Lemmas.lean:354-380`. The dual-span results require finite-dimensional V or finite E and do not assert scalar extension. The tower kernel lemma concerns cancellation when the original domain already has extended scalars; the restriction-of-scalars kernel lemma and intermediate-subfield intersection lemmas use different constructions. The tensor-basis equivalence supplies coordinates but is not the common-kernel statement or a one-line specialization of it. There is no claimed Mathlib match for the item.

Searched all DAG statements/titles/sources for 00CX, 059R, 059M, tensor bases, vector-space bases, common kernels and simultaneous equations. Existing `lem-weil-pbc-vector-space-free` supplies basis existence; `def-weil-pbc-module-tensor-product` explicitly supplies generation, the universal property and bilinearity. Also read the related scalar-extension definition, the existing Galois-invariants tensor result, the subspace-complement leaf, and the family-detection node before deciding none needs duplication. Whole-blueprint searches for `common kernel`, `linear functionals`, and `basis` found no alternate statement of this item (the Engel common-kernel lemma concerns nilpotent Lie algebras). No new node was created.

## Not duplicates

No new node exists in this delivery, so there are no new/existing pairs to justify. The adjacent family-detection theorem was reused as background evidence only, not duplicated or misrepresented as an exact attachment.

## Review by Q02

I read the actual statement and proof of Stacks Tag 00CX (`algebra.tex:1715-1785`), which constructs the tensor product by bilinearity relations and explicitly says that pure tensors generate it, and Tag 09FN (`fields.tex:154-162`), which says every vector space has a basis. I checked both tag/label associations in `tags/tags`. I also read 059R's free-module example, while deliberately using the direct coefficient calculation instead of a tensor/product theorem. There are no new-node sources to audit.

For step 1 I opened the full statement of `def-weil-pbc-module-tensor-product` and checked that its universal property applies to the displayed F-bilinear map into the F-vector space L. The proof checks L-linearity on generators by the written formula, and equality then extends to sums because those generators span. It does not take a theorem about exactness or products from a definition.

For step 2 I opened `lem-weil-pbc-vector-space-free`: it explicitly says that every vector space has a basis, with no finite-dimensionality hypothesis. L is an F-vector space because F is a subfield. This is the sole non-elementary step and cites that existing Mathlib leaf, not just a definition of freeness. The finite-expansion and linear-independence properties are the meaning of basis, made explicit in the step.

For step 3 the cited tensor-product node explicitly says pure tensors generate as an F-module. Each F-coefficient can be absorbed into a first tensor factor by bilinearity. Expand only the finitely many second factors in the chosen F-basis of L, take the finite union S of their supports, and regroup with the written formula v_i = sum_j c_ji w_j. This is a direct finite sum calculation, not a hidden tensor-basis identification. In particular, uniqueness of a tensor-coordinate expansion, commutation with infinite intersections, and exactness of tensoring are not assumed.

For step 4 the cited tensor-product statement provides bilinearity; the extended functional's formula and linearity were established in step 1. Each u_e(v_i) belongs to F by the original codomain hypothesis. Thus the finite scalar relation in L is exactly an F-linear relation among the chosen independent b_i, and its coefficients vanish. This holds for each e separately, so every v_i lies in K even for infinite E. The formula b_i * (v_i tensor 1) = v_i tensor b_i uses precisely the action on the second factor specified in the item. No assumption that a finite subset of E detects the kernel is introduced.

For step 5 no node is cited: its only input is the preceding construction and the statement's definition of K. Each generator evaluates to zero, and the written finite-span argument gives the converse inclusion. This final elementary step includes E empty: K = V and the expansion from step 3 spans the entire tensor product. It also covers V = 0, all functionals zero, E a singleton, L = F, infinite-dimensional V, infinite E and infinite degree L/F. The finite support used belongs to each tensor, not to any global dimension or equation bound. None of the five steps exceeds 2000 characters; their total text is under 3000 characters.

Against delivery-errors B: there are no new unsplit nodes or missing new-node hypotheses, and the unchanged statement introduces every object. Against C: I verified every `uses` statement directly and generated verbatim quotes in `citations.json`; the proof-dependency union is exactly the tensor definition and the basis leaf. Against D: the proof carries the argument in its own steps and creates no restatement node; there is no recursive dependency or unstated induction. Against E: checked all hypotheses and the scalar field of each relation, and wrote out the finite regrouping and action formulas. The direct proof avoids any false claim that tensor products commute with arbitrary products.

## Unfinished work

None in the stage-1 split. This delivery contains no Lean proof claim; the Mathlib leaf for basis existence is already in the DAG. Required server checks and final push are performed by the prescribed delivery tool.
