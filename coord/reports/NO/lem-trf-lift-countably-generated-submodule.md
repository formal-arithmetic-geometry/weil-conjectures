# Stage-1 delivery: lem-trf-lift-countably-generated-submodule

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-lift-countably-generated-submodule.json`: statement, now split; no exact Mathlib match. The statement is unchanged. Four elementary proof steps replace the empty proof.
- `citations.json`: verbatim statement excerpts for both proof-step citations.
- `searches.jsonl`: actual search-command log, retained in the sandbox.
- `report.md`: this report and signed mathematical review.

New nodes: 0. New Mathlib leaves: 0. No units, Lean files, live repository files, or launcher files were written. This is an auxiliary descendant, not the key statement of its unit, so no unit realization record is changed.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, the item id, countably generated modules, countable tensors/submodules, and lifting terminology. No project declaration states this item. The broad lift/submodule search returned unrelated quotient lifts, homogeneous polynomial submodules, and faithfully flat family descent; none asserts countable generation of a lifting submodule. The source node has no Lean audit attachment. Upstream master sorry declarations were not treated as proofs.

## WANTED

None. The item's source and the source of the sole cited definition are present locally.

## Corrections and source audit

The imported node had an empty proof and already had the correct tensor-product statement dependency. Its statement, including the image-containment conclusion and absence of flatness, is correct. No statement dispute or hypothesis change is needed.

Read `literature/stacks-project/algebra.tex`, lines 22424–22436, and verified `05A7,algebra-lemma-lift-countably-generated-submodule` in `tags/tags`. The source writes the module factor first; our item writes the ring-extension factor first. The same finite-sum argument is written directly in the item's convention, with the B action on the left, rather than invoking any extra comparison lemma. Also read the adjacent Tag 05A8 proof and the immediate parent node's Step 2: precisely the countably generated coordinate submodule is passed to this lemma. The stronger conclusions of the parent are not used here.

Read the unit `sk-i-curve-zero`, its chapter record, the current main-20261015 ancestor's statement/proof, and the inherited blueprint ancestry. This small algebra lemma supports the already recorded flatification/projectivity-descent chain beneath the normal-cone/specialization argument; it does not replace the unit's route. Its blueprint ancestry and non-unspecified place are retained, and `same_as` was checked.

Searches of the whole DAG by `05A7`, source label, and countably generated/tensor terminology found the item and its parent, not a second statement of the lifting lemma. Whole-blueprint searches with `tools/blueprint_refs.py search` for `05A7`, `countably generated`, and `finite sum of pure tensors` returned no matches. No new node was justified: countability of the displayed double-indexed family and the linear-span argument are short elementary steps, not new lemmas.

Ran the prescribed msearch.py tools with this item id, preserving the pre-existing search records and appending the actual new query text and command-log results. LeanFinder was tried with two phrasings; LeanSearch and Loogle also ran. Read the actual local Mathlib candidates: `TensorProduct.exists_of_fg` in `Mathlib/RingTheory/TensorProduct/DirectLimitFG.lean:202–206`; `Submodule.exists_fg_le_subset_range_rTensor_subtype` and its inclusion variant in `Mathlib/RingTheory/TensorProduct/Finite.lean:48–55,66–73`; and the finite tensor-decomposition and finite-submodule results in `Mathlib/LinearAlgebra/TensorProduct/Finiteness.lean:58–99,131–146`. These concern one tensor or a finite set, not a countably generated B-submodule and one countably generated A-submodule. They are therefore candidates for proof ingredients, not exact leaves for this item. The existing tensor definition already supplies all ingredients used by our proof, so none of these finite-extraction lemmas is cited as a black box.

Two initial grep calls mistakenly included a redundant `Mathlib` prefix in the optional subdirectory. Their zero-hit outputs are retained as inconclusive, explicitly not used to assert absence. Corrected calls with `LinearAlgebra` and `RingTheory/TensorProduct` ran; the latter located the finite-extraction declarations above. No unavailable service was reported as no match and no unrun search was added.

## Unfinished work

None in this one-level split. No new unsplit prerequisite is introduced. Verification and delivery results are reported by the required delivery command.

## Not duplicates

No new nodes are created. Reused `def-weil-pbc-module-tensor-product` instead of creating a finite-tensor-expansion lemma or another tensor definition. The adjacent adapted-submodule node is the parent using this result, not a replacement theorem available to prove it.

## Review by NO

I read Tag 05A7's actual statement and entire proof, not just its tag, and checked each of the four steps against it. The proof has no non-elementary prerequisite beyond the contents of the existing tensor-product definition. The short enumeration and linear-combination arguments are fully written, so no mathematical content has been moved into a renamed copy of the item.

Step 1 uses `def-weil-pbc-module-tensor-product` exactly for generation by pure tensors and bilinearity. Its statement explicitly says that the tensor product is generated by the elements x tensor y. Finite A-coefficients are absorbed into the B factor using the displayed balancing formula; the generator set is indexed by a subset of the natural numbers rather than assuming an infinite nonempty set. The rings are commutative and B is an A-module through the supplied homomorphism, as the definition requires. The chosen expansions have finite length, including zero length.

Step 2 has no cited theorem: P is the span of precisely the factors chosen in Step 1. I wrote a diagonal enumeration of pairs of natural numbers to check at-most-countability of the family. Images and subfamilies of that explicit enumeration give the required countable generating subset. Taking the span does not assert that the underlying set of P is countable, which would be false over an uncountable ring.

Step 3 uses the same definition exactly for its universal property for A-bilinear maps; that entire clause is quoted in citations.json. Applying it to (b,p) maps to b tensor iota(p) constructs the natural map. I checked B-linearity on a pure tensor by multiplication in B, then extended by additivity. This makes the range a B-submodule without assuming that tensoring an inclusion is injective. The source and target B-actions are specified in this step.

Step 4 uses only the explicit map from Step 3 and finite combinations from the definition of generation: z_i is an actual preimage for q_i, and a finite B-linear combination of the z_i lifts every member of Q. It cites no additional node and uses no exactness or flatness theorem. Both cited uses from Steps 1 and 3 have verbatim excerpts from the opened definition statement; neither uses something found only in a cited node's proof. The union of all step uses is exactly proof_deps, consisting of that definition alone, so the change adds no circular edge or off-route statement tool.

I tested Q=0 (choose no generators and P=0), finite and countably infinite generating families, zero tensor summands (empty sums), L=0, B=0, A=B, and the nonflat map Z to Z/2. In the last case the method still proves image containment: it never identifies B tensor P with a submodule of B tensor L. For example P=2Z inside L=Z illustrates why that map need not be injective, and our argument does not need it to be. Repeated factors or redundant generators do not affect the construction. No faithful flatness, projectivity, Noetherian assumption, or countability assumption on the rings is used.

Against delivery-errors B–E: the statement introduces every object and defines countably generated inline; the only further notion has its existing definition dependency; the tag and label are verified; source and formulas are written in TeX; there are no new node matches, incomplete new statements, duplicates, item-clause relabelings, circular dependencies, hidden standard lemmas, or hypotheses taken from a parent. All four steps are elementary arguments from the definition and their preceding constructions, each below 600 characters; there is no long non-elementary step to extract. The original statement and maintainer-owned metadata are retained. I corrected the initially invalid grep scopes and recorded their outputs honestly. No SGA source, Lean editing, compiler, Lake, or local preflight/check_dag/review_split execution was used.
