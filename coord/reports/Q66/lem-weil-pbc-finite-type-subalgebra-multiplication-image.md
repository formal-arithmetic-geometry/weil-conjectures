# Stage-1 report: Q66

## 1. Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-subalgebra-multiplication-image.json`: existing statement, split into four steps. Full sheaf theorem has no Mathlib match; existing DAG results provide the non-elementary ingredients.
- `citations.json`: one verbatim statement excerpt for each step/node citation.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files, source repository files, compiler outputs, unit records or launcher files were written.

## 2. Attachments

None. Searches for the exact item id, its blueprint docstring tag, finite type subalgebras and multiplication-image terminology in `lean/WeilConjectures/` found no declaration stating all clauses. The existing quasi-coherent tensor and module-image declarations state ingredients and are cited as such, not claimed as attachments for this item.

## 3. WANTED

None. All sources used are already in `literature/`.

## 4. What was wrong or incomplete

The item statement is correct and is retained byte for byte, as are its statement dependencies, inherited provenance and previous Mathlib-search entries. Its proof was empty. Properties Tag 05JT (`lemma-algebra-directed-colimit-finite-type`, lines 3349–3372) explicitly omits the details of the multiplication-image assertion. This split supplies those details rather than citing another node restating that assertion.

The inherited blueprint origin names historical ancestor split step 4. I read the current main-20261015 ancestor and its `blueprint_update`: finite-pushforward embedding is now step 2 of that proof. The repaired blueprint.from.place now names current step 2 explicitly. The present work is the same finite-algebra approximation subargument below that embedding. Chapter and unit records were read; no change to either is needed.

Mathlib search commands ran through the mandated `msearch.py` interface and were read. LeanFinder returned finite submodule/tensor finiteness lemmas; LeanSearch returned `Subalgebra.mulMap_range` and ring tensor-map statements; Loogle confirmed `Subalgebra.mulMap_range`; broad grep found no sheaf multiplication-image theorem. A second grep located `Subalgebra.mulMap_tmul` at Mathlib/LinearAlgebra/TensorProduct/Subalgebra.lean:217 and `Subalgebra.mulMap_range` at line 231; I read lines 197–242. These apply to subalgebras of a commutative ring/semiring, and do not prove the item's sheaf construction, image quasi-coherence, or affine-section comparison. The different natural-language queries and these source reads distinguish the full item from its elementary ring-level calculation. The ring calculation is written as a step and generates no new node. All current commands are recorded exactly in `searches.jsonl` and appended to the item's searches; inherited searches were preserved as historical records.

## 5. Unfinished work

None in the natural-language split. No new unsplit nodes or attachments are proposed. Independent maintainer review remains the delivery process's responsibility.

## Not duplicates

No new nodes were created. Whole-DAG tag and keyword searches and whole-blueprint searches for `subalgebra`, `quasi-coherent tensor`, `multiplication image` and `05JT` were read. The relevant existing generic nodes were reused: `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`, `lem-weil-pbc-quasi-coherent-module-cokernel-image`, and `lem-weil-pbc-affine-opens-basis`. The ringed-space algebra-image node is unnecessary because the elementary finite-sum argument proves subalgebra closure here. Blueprint ring-level directed-union nodes do not state this sheaf theorem. `same_as` remains empty.

## Review by Q66

I read Properties Tag 05JT and its surrounding definition of finite type quasi-coherent algebras, the current main-20261015 blueprint ancestor, and the parent split. This verifies why the item is needed and why it requires no quasi-compactness or quasi-separatedness: those hypotheses enter the parent's global approximation argument, not this construction. I also read Modules Tag 01CA (`section-tensor-product`, lines 2272–2331), Sites, Modules Tag 03CY (`lemma-sheafification-presheaf-modules`, lines 815–867), Schemes Tag 01I8 (`lemma-widetilde-constructions`), Tags 01IB/01IC (affine quasi-coherent equivalence and kernels/cokernels), Section 01LA, and Tag 01IT (`lemma-basis-affine-opens`). Tags were checked against `tags/tags`. No SGA source is used. There are no new nodes requiring a separate source audit.

For step 1 I opened all four cited node statements. The algebra-sheaf definition supplies the structure maps and multiplication; the module tensor node explicitly states both its bilinear universal property and generation by pure tensors. The module-sheafification node explicitly gives unique factorization of module-presheaf maps, while the tensor-sheaf definition identifies the domain as precisely that sheafification. The argument checks the two scalar identities and restriction compatibility before applying the factorization. It also proves uniqueness, rather than only constructing a map. This step is elementary from those universal properties; it does not presume that the presheaf tensor is already a sheaf.

For step 2 I read both entire cited statements, in particular the actual canonical map t_U and the image node's locally defined subsheaf and affine image equality. Both inputs B_k are quasi-coherent by hypothesis, so the tensor theorem applies; its output is quasi-coherent, and A is quasi-coherent by hypothesis, so the image theorem applies to mu. The identification of C with that module image uses exactly the same local-section definition. The equality of affine images follows from surjectivity of t_U and mu_U t_U = nu_U. It does not assume that taking sections preserves arbitrary sheaf images. This is the only non-elementary step, and both results are existing nodes of the same unit.

For step 3 I reread the pure-tensor-generation clause and the affine-basis statement. Finite linear combinations can have their scalar coefficients absorbed into B_1, so the image consists of finite sums of products. The displayed double-sum identity uses commutativity of A; units in the two unital subalgebras give both inclusions and the scalar image. Minimality follows since every subalgebra containing both factors contains all these sums. For arbitrary W the affine-basis node supplies affine opens contained in W, and the already established submodule-sheaf property gives local membership descent for a product or unit. Thus no affinity of intersections or injectivity of the tensor multiplication map is asserted. This is an explicit elementary argument, not a separate sheaf-algebra comparison theorem hidden in the step.

For step 4 I opened the cited finite type subalgebra definition. It says finite generation as an algebra on every affine open, which is exactly the property proved. The two inclusions for the subalgebra generated by the combined lists prove the stated generators, without importing a finite-type tensor theorem. I checked empty lists (the algebra is the scalar image), B_1 = B_2 (mu need not be injective), B_1 = R[x^2] and B_2 = R[x^3] inside R[x] (the output is R[x^2,x^3], not necessarily R[x]), zero section rings and the empty scheme. The arguments remain valid. No reducedness, flatness, nonzero ring, separatedness or finiteness as a module was used.

Against delivery-errors B–E: there are no new nodes to duplicate or restate a clause; every non-elementary inference is step 2 with exact existing statements; all citation excerpts were mechanically checked to be verbatim substrings, including universal properties rather than merely definition names. No proof of a cited node is used as an extra hypothesis. Dependencies are the union of uses, with no parent or descendant citation. No off-unit tool declaration is needed. All four steps are below 2000 characters; the elementary calculations are written out. The original statement and dependencies have not been weakened or changed.


## Repair of the refused landing (2026-10-22)

The sole return was a failed promotion of a side-project completion into the live DAG, after the reader had approved the mathematics. I continued the retained delivery rather than replacing it. Its pre-existing dry-run receipt named head `0d2ab963aee`; the first dry run in this repair rebuilt that retained work against the current server DAG and passed at `77b8c79830d`. The delivery command performs the rebase in its own temporary worktree; no git command or write was made in the shared read clone.

I compared the retained item with the current repository item field by field. The current item is still unsplit with an empty proof. Its statement, statement dependencies, source, creation provenance, chapter, unit and inherited searches agree with the retained version. The retained additions are the four-step proof, its dependencies and origin, the five logged search records, split status and split report. All earlier searches and their recorded results were reread and retained; the mathematical search questions have not changed.

I reopened every current proof dependency: `def-weil-pbc-comm-algebra-sheaf`, `def-weil-pbc-module-tensor-product`, `def-weil-presheaf-modules-sheafification`, `def-pur-sheaf-tensor-product`, `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`, `lem-weil-pbc-quasi-coherent-module-cokernel-image`, `lem-weil-pbc-affine-opens-basis`, and `def-weil-pbc-finite-type-quasi-coherent-subalgebras`. The nine retained quotations remain verbatim in these current statements. Their full statements still supply respectively the algebra operations, bilinear universal property and generation, unique module-sheafification extension, sheaf tensor domain, canonical affine tensor comparison, quasi-coherent local image and affine image equality, affine covering basis, and finite algebra generation on every affine. Thus the current versions support the same applications and require no stronger hypotheses. I also reopened all statement dependencies and the current parent and blueprint ancestor; the current parent still invokes this item precisely to obtain a common upper bound for two subalgebras.

Two concrete corrections accompany the rebase. First, the inherited blueprint place referred to historical ancestor step 4; the current ancestor's proof and main-20261015 update put the finite-pushforward embedding in step 2. I updated blueprint.from.place and split_report.blueprint to that current place while preserving the ancestor and via chain. Second, in proof step 3 I replaced the ambiguous phrase about products in A(W) with explicit s,t in C(W), checked their affine restrictions, and wrote why the local products and unit agree on overlaps and glue in the subsheaf C. This proves precisely closure of C, without asserting that arbitrary products in A belong to C. No theorem statement, hypothesis or dependency changed.

For this repair I reread Stacks 05JT's omitted-details passage, Modules 01CA, Sites, Modules 03CY, Schemes 01I8, 01IB, 01IC, 01LA and 01IT, and the previously found Mathlib Subalgebra.mulMap/mulMap_tmul/mulMap_range source. I repeated the small-case reasoning: empty scheme and zero rings, empty generating lists, identical factors, and R[x^2], R[x^3] inside R[x]. The affine computation and the new explicit sheaf-gluing wording work in all these cases; no affine intersections, flatness, quasi-compactness or quasi-separatedness are needed. Every step remains below 2000 characters, every non-elementary application is cited, and no new node or hidden auxiliary lemma has been introduced. The original detailed Review by Q66 above remains my substantive review, with these corrections added under the same signature.
