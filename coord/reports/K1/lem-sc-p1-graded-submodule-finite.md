1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-p1-graded-submodule-finite.json`: item, statement, split proof, Mathlib searches retained, split status.
   - `dag/nodes/sec-picard-framework/lem-sc-p1-ungraded-submodule-finite.json`: statement-only Mathlib leaf; the ungraded Noetherian submodule fact matches `isNoetherian_of_isNoetherianRing_of_finite` together with `IsNoetherian.noetherian`.
   - `citations.json`: citation quote for step 1.

2. Attachments: none.

3. WANTED: none.

4. Problems found: the imported item had no proof and was marked unsplit. No exact declaration with the blueprint tag exists in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; no existing DAG or blueprint node states the graded-submodule result. The proof was split at the actual mathematical boundary: ungraded finite generation from Noetherianity, then homogeneous-component extraction.

5. Unfinished: none.

## Review by K1

I read the item source, `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-duality/lem-sc-p1-graded-resolution.md`, at the sentence “Noetherianity keeps the successive graded kernels finitely generated”, and read the parent node `lem-sc-p1-graded-resolution` to confirm this is the exact route. I searched the whole DAG and blueprint for graded-submodule and Noetherian-submodule statements, and searched the Lean source for the item tag and relevant names; there is no existing exact declaration or duplicate node.

Step 1 cites `lem-sc-p1-ungraded-submodule-finite`. Its statement explicitly has a field `k`, the ring `S=k[x_0,x_1]`, a finitely generated S-module `N`, and an S-submodule `K`, and concludes that K is finitely generated. These are exactly the hypotheses and conclusion used after forgetting the grading. The node's Mathlib match was checked in `Mathlib/RingTheory/Noetherian/Basic.lean` lines 324-328 (`isNoetherian_of_isNoetherianRing_of_finite`) and `Mathlib/RingTheory/Noetherian/Defs.lean` lines 63-65 (`IsNoetherian.noetherian`); its field and polynomial-ring hypotheses specialize in one line. Step 1 is therefore non-elementary and cites that node.

Step 2 is elementary: a graded element has finitely many homogeneous components, and a graded submodule contains each component. Replacing each finite ungraded generator by its finitely many components gives a finite homogeneous generating set. I explicitly checked the zero submodule case and did not cite a node for this direct decomposition argument.

The new node is statement-only because it is a Mathlib leaf, has no proof or proof dependencies, carries its own complete statement and the finite-generation definition dependency, and includes LeanSearch, Loogle, and source-grep searches. The item has `blueprint.from.place` filled, `same_as: []`, a two-step proof, and `proof_deps` equal to the cited node. TeX escapes and the citation quote were validated by JSON parsing.
