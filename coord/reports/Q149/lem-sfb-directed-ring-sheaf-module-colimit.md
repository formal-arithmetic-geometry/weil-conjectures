# Stage-1 report: lem-sfb-directed-ring-sheaf-module-colimit

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-directed-ring-sheaf-module-colimit.json`: item, statement unchanged, split into seven steps; not a Mathlib leaf.
- No new DAG nodes and no new Mathlib leaves.
- `citations.json`: every proof-step citation, with the cited statement copied verbatim.
- `searches.jsonl`: actual search-command log retained in the sandbox.

## Attachments

None. Searching the specified source checkout for the exact blueprint tag and ring/module/sheaf colimit terminology did not find a project declaration stating this entire comparison. The module-sheaf colimit results do not state the additional ring-to-module comparison. The upstream master reference is not treated as proof evidence.

## WANTED

None. The literature needed for the ingredients is present.

## Findings and changes

The item was an unsplit agent assembly, with an empty proof and no Lean audit claiming a finished proof. Its source explicitly says that the comparison is not a single lemma in Stacks. I retained its statement and all original search records. The new proof is therefore honestly marked `proof_origin.by: agent`, using Stacks Modules on Sites, Tag 03DB (`lemma-limits-colimits`) and Tag 03EP (`lemma-tensor-commute-colimits`), item (2). I read their statements and proofs in `literature/stacks-project/sites-modules.tex`, together with the tensor construction in Section 03EK and the module-sheafification universal property in Tag 03CY.

The construction forms a module colimit L, puts multiplication on L using common upper stages, checks all ring laws, and then uses the given ring-colimit universal property of A to obtain an inverse A -> L. It does not assume that sections of A or L are globally represented at a stage. The last step explicitly proves the requested factorization of each module cocone.

The chapter and unit records were read. This supplies the first sentence of the current blueprint proof of `lem-sfb-qlbar-flat`: passage from the directed ring coefficient colimit to the underlying E_X-module colimit. Neither the chapter route nor the finite-extension compatibility unit changes. This item is not the unit's key statement, so its unit record is untouched.

Whole-DAG statement/title searches, Stacks-place searches, and blueprint searches for colimit, diagonal, ring sheaves, underlying module, and tensor colimits found no existing node stating the whole item. The directed tensor cocone node concerns ordinary rings with specific base-change presentations and is not an arbitrary-site theorem. The ring-sheafification-underlying-abelian node concerns topological spaces, so it is not applied on a general site. Existing generic module-colimit and tensor-colimit statements suffice, and no duplicate or clause-restatement node is created.

Mathlib was searched with the prescribed command in all four modes, including a second semantic phrasing about commutative monoid objects. I read the returned module-sheaf colimit file and the ordinary-ring filtered-colimit instances (CommRingCat, Ring/FilteredColimits.lean:355,363). These give existence or different underlying categories, not this comparison. A grep request for `CategoryTheory/Monoidal/Mon` was an invalid subdirectory and is recorded as such, not as absence evidence; it was followed by a read/search of the existing `Mon.lean` file. No unavailable service was recorded as a negative result.

## Review by Q149

I compared the unchanged item to its actual source description: it is an assembly from the module-colimit and tensor-preservation facts, not a verbatim Stacks theorem. I read the current blueprint's first sentence and retained its ring-to-module purpose. No hypotheses were added or dropped: I remains a small nonempty directed poset in the coefficient universe, all maps are unital, the base ring is commutative, and both scalar compatibility equations are retained. Essential smallness relative to w permits sheafification and the module colimit in that universe. The site is never assumed to have enough points, finite covers, or sectionwise sheaf colimits.

Step 1 cites `lem-weil-pbc-module-sheaves-colimits-forgetful`, whose clause (2) really gives the colimit in Mod(R); it is not used to claim a ring colimit. The definition nodes for modules and category colimits provide the linearity equation and the unique induced map u. Scalar compatibility is checked explicitly before applying the module result.

Step 2 uses the statements of `def-pur-sheaf-tensor-product` and `def-weil-presheaf-modules-sheafification`: tensor is the sheafification of the sectionwise tensor and maps to a module sheaf extend uniquely. Multiplication at a common stage is balanced because the scalar maps and transitions are compatible. The text proves independence of the upper bound by passing to a further common upper bound, and proves transition compatibility the same way. This is a short calculation with the definitions and cocone equations; I marked that calculation elementary. No general preservation theorem is claimed from a definition.

Step 3 cites `lem-weil-pbc-independent-sheaf-tensor-colimits`, whose statement explicitly allows the independent site and coefficient universes of the item and preserves coefficient-sized diagrams. It provides both successive colimit factorizations; the first-variable version uses the explicit inverse tensor swaps. The resulting product and the equality test on b_i tensor b_j are derived from the two successive universal properties in the step, not asserted from a diagonal-cofinality theorem that has not been cited.

Step 4 uses that same tensor-preservation statement successively for three variables, and the tensor definition for the canonical association. A common upper bound of three indices is obtained by two applications of directedness. The two parenthesizations are calculated in that one stage. The text checks commutativity, both unit laws, distributivity, and the unital multiplicativity of every b_i. Nonemptiness is used exactly to choose the common unit. No global representation of arbitrary sheaf sections is used.

Step 5 uses the tensor-preservation statement for checking the scalar action and multiplicativity of u. The module definition supplies the scalar-linearity equation. The base map s_L is b_i s_i for every i; this proves it is a unital ring map. The action on L really is its original R-module action, which is essential for the next step. The product calculation for u uses the actual ring maps q_k, so u is proved to be a ring map before the ring universal property is used.

Step 6 cites precisely the category-colimit and module definitions. The given ring-colimit property gives v with v q_i = b_i. The computation v s = s_L makes v linear, and the two inverse equations use the appropriate universal properties: module uniqueness for vu, ring uniqueness for uv. This step does not infer that a mere additive map is multiplicative. Step 7 uses only the module-colimit universal property from step 1 and these inverse equations to prove existence and uniqueness of f with the actual legs q_i.

All cited node files were opened and their statements read; `citations.json` copies those statements, not material from their proofs. The two off-unit generic tools are declared in `split_report.tool_uses`; they provide basic module and tensor infrastructure rather than an alternative coefficient route. No step exceeds 2000 characters, and the steps contain the construction itself rather than concealing a separate lemma or moving the item's conclusion to a new node.

For small cases I checked a singleton I (the product and inverse reduce to the given stage), a zero coefficient ring (all unital R-algebras and their modules are zero), a diagram with a noninjective ring transition (the common-stage formulas still work without cancellation), and incomparable indices with a common upper bound (the further-upper-bound calculation is exactly the required independence). On a site with an empty covering the unit can equal zero on the forced zero sections; the same ring laws hold. The proof is valid for sites without points because every test is an equality of morphisms detected by a categorical colimit, not a stalk argument. I found no statement dispute. The only search correction was rejecting the invalid directory grep as evidence.

## Unfinished work

None in this one-level split. Independent maintainer review remains the next project stage after direct delivery.
