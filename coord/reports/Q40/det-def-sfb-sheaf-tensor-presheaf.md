## Files written

- `dag/nodes/sec-proetale-coefficients/det-def-sfb-sheaf-tensor-presheaf.json`: definition with its original statement and a complete seven-step construction/proof, status `split`. No new nodes and no new Mathlib leaves. The existing small-limits leaf `lem-coef-grothendieck-small-limits` supplies the one non-elementary infrastructure theorem.
- `citations.json`: one verbatim statement quotation for every use in steps 3, 4, 6 and 7.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

## Attachments

None. I searched the exact blueprint tag and id, and the notions presheaf tensor, internal hom and closed functor category under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`. The project sheaf-level declarations in `CategoryTheory/GrothendieckAbelian/Monoidal/TensorColimits.lean` concern sheaves and do not state the object's slice-end construction and both Hom formulas. The master checkout is reference material only; it was not treated as a finished proof.

## Wanted literature

None. I read the current main-20261015 item, chapter `_section.md`, and unit `_section.md`, the pinned Mathlib source files specified below, and Stacks `injectives.tex`, Definition Tag 079B (`definition-grothendieck-conditions`). No SGA source was used.

## What was wrong or incomplete

The item has no `lean_audit`, `chapter` or `unit` fields. The expected records `dag/chapters/sec-proetale-coefficients.json` and `dag/units/sk-def-sfb-sheaf-tensor.json` are absent. I read the corresponding current blueprint `_section.md` files instead and left maintainer metadata untouched. The unit has a statement, not proof steps; its route here is the ordinary presheaf structure used before sheafification. This item is not that unit's key node, so no unit realization record is due.

The original proof's sentence about products over a set of objects of an essentially small slice concealed a size reduction: an essentially small category can have a large collection of objects. Step 2 now chooses a small full slice subcategory, and step 3 explicitly extends the resulting wedge along isomorphisms to every slice object. The unit explicitly fixes essential smallness relative to the Hom universe of the coefficient category; the proof uses that existing convention. The statement is unchanged, and no statement dispute or added mathematical hypothesis is needed.

The current item Markdown contains no proof section, although the imported node's `proof_origin.place` said `## Proof`. The new proof is therefore explicitly marked agent-written and its source places refer to the actual definition clauses and Hom formulas. It includes all details, rather than asserting that the current Markdown has a written proof.

The diagonal internal-Hom values are not a covariant diagram on the slice: restriction maps are contravariant in both presheaves and mixed in internal Hom. Step 3 spells out the mixed-variance bifunctor (indexed by the opposite slice), the two equalizer maps, and the exact wedge equation. Reindexing the opposite slice describes the same conventional end written in the statement. The later steps spell out every naturality condition instead of assuming that objectwise currying gives the presheaf adjunction.

## Mathlib findings and duplicate search

All Mathlib queries were run only with `/home/ubuntu/weil-launcher-nt/msearch.py Q40 det-def-sfb-sheaf-tensor-presheaf ...`; the item's `mathlib_searches` repeats the exact tool/query strings and summaries of their recorded results. Two distinct semantic phrasings were tried for both the full item and generic ends. Loogle, LeanFinder and LeanSearch succeeded. The first grep used a nonexistent directory-shaped guess for the functor-category file and found no hits; later source-directory searches found the actual files, and that empty query is retained honestly.

The source read was:

- `Mathlib/CategoryTheory/Monoidal/FunctorCategory.lean`: `CategoryTheory.Monoidal.FunctorCategory.tensorObj` at line 43; `functorCategoryMonoidalStruct` at line 85; `functorCategoryMonoidal` at line 160; `functorCategorySymmetric` at line 197. These give clause 1 exactly.
- `Mathlib/CategoryTheory/Enriched/FunctorCategory.lean`: `diagram` at line 51, `enrichedHom` at line 63, `HasFunctorEnrichedHom` at line 295, and `functorEnrichedHom` at line 309. This is the matching end-valued construction, using under-categories for a covariant functor category, corresponding to opposite slices for presheaves.
- `Mathlib/CategoryTheory/Monoidal/Closed/FunctorCategory/Basic.lean`: `homEquiv` at line 48, `adj` at line 129, `closed` at line 139, `monoidalClosed` at line 145. They assume the global/slice enriched ends exist, rather than proving their existence for the essentially small slices in this item.
- `Mathlib/CategoryTheory/Monoidal/Closed/FunctorCategory/Complete.lean`: `functorCategoryMonoidalClosed` at line 87 obtains an abstract right adjoint and expressly disclaims useful definitional properties. Its bare existence statement does not identify the specific internal hom or give the local parameter-object formula.
- `Mathlib/CategoryTheory/Limits/Shapes/End.lean`: `end_` at line 214, projections at line 218, wedge condition at line 221, `hom_ext` at line 228, `lift` at line 238 and `lift_π` at line 242. I read their types and universal property.
- `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/Basic.lean`: `IsGrothendieckAbelian` at line 70 and `IsGrothendieckAbelian.hasLimits` at lines 102–104. This is already recorded by the existing completeness node.

I did not make the item a leaf merely from the class instance: its end-existence hypotheses and the local Hom formula still require the explicit small-diagram/wedge arguments. The close match is recorded in `mathlib_candidate`. I initially considered a generic end-definition leaf, then folded the equalizer construction and its universal property into the item: it is a short direct use of the existing completeness statement and definitions, so a separate node would add no mathematical work.

I searched the entire DAG by generic-end, multiequalizer, completeness and monoidal keywords and ran `tools/blueprint_refs.py search` for `presheaf tensor`, `closed symmetric`, `objectwise tensor product`, `end over`, `small limits`, `bifunctor` and `universal wedge`, among other queries. The whole statement has no other blueprint equivalent; `blueprint.same_as` is `[]`. The sheaf-tensor structure and closedness nodes are downstream, not interchangeable presheaf statements; neither was cited back. The existing `def-sp-grothendieck-abelian` and `lem-coef-grothendieck-small-limits` were read in full and reused. Since no node is created, there are no new/existing tag pairs requiring a Not duplicates section.

## Unfinished work

No mathematical step is deferred to a new unsplit node. No Lean file was written or compiled. No build, Lake command, direct git command, live-project edit or push was performed. The required delivery dry run performs the mechanical validation and is invoked with `--no-push`.

## Review by Q40

I checked the statement against both clauses and both displayed Hom formulas of the current main-20261015 source, and read the full unit statement to verify the universe convention and that this is the presheaf construction preceding sheafification. I did not import the closedness of sheaves into the presheaf argument. The Grothendieck assumption means exactly the definition in `def-sp-grothendieck-abelian`, which matches Stacks Tag 079B; its small-limit consequence is exactly the separately existing Mathlib leaf, not a consequence I attributed to the definition node.

For step 1, tensor is a bifunctor by the hypothesis that the coefficient category has a symmetric monoidal structure. Functor laws, naturality and all coherence diagrams are checked after evaluation, where they are the assumed coefficient-category diagrams. This is a direct construction and uses no additional theorem. For step 2, I checked that slice representatives require all arrows from the chosen representative domains to U, rather than merely a skeleton of C with U in it. These arrows form a small set because the Hom sets are small. Every original slice object has an explicitly exhibited isomorphism to such a representative. This proves the size reduction rather than citing an unrelated limit-existence result for a large category.

For step 3, I reopened the cited completeness node: it provides every small diagram's limit and the exact existence/uniqueness of cone maps, which are precisely what this step uses for the two discrete products and the equalizer. I checked each equalizer component has codomain h(F(V_j),G(V_i)); this fixes the variance. The extension map uses inverse restriction maps only for the chosen isomorphisms, never for an arbitrary restriction. I checked independence with b inverse composed with a, and the wedge equation for a general slice arrow with b inverse composed with c composed with a. Thus no unproved theorem on invariance of ends under equivalence is invoked.

For step 4, the only cited result is again the small-limit node's uniqueness clause. The reindexed projections satisfy the already-written wedge equation, so they produce the restriction map; checking its projections proves both presheaf laws and variance in F and G. For step 5, the tensor–Hom equivalence is a hypothesis, and applying its naturality to the previous wedge equation gives exactly G(a) composed with phi_w equals phi_v composed with (F(a) tensor identity). There is no claim that h(F(U),G(U)) itself has presheaf restrictions.

For step 6, the completeness node is cited for the unique map into the equalizer, not for a tensor-adjunction theorem it does not state. The two displayed calculations establish first the wedge condition and then naturality in U for the proposed psi. The order H(v)=H(a)H(w) follows from contravariance and v=w composed with a. For step 7, the arrow in C/W is explicitly (V,a) to (W,id), so the wedge calculation yields exactly the naturality equation for chi. Evaluation at identity slice arrows and uniqueness into the limit prove both inverse identities. The last three component formulas separately check naturality in F, H and G. Each citation in these four steps has a verbatim quote in citations.json; the quote contains the actual small-limit universal property used. No step quotes a theorem from another node's proof.

I tested the constructions on the empty category (no values to construct), the one-object identity category (the equalizer reduces to the coefficient internal hom), the arrow category (the wedge is exactly one naturality square), zero F or G in the abelian coefficient category (the internal hom and its adjunction give the zero object), and F equal to the constant tensor unit (families are determined by the identity slice arrow and give G(U)). For a large category equivalent to a small one, the chosen-representative formulas avoid a large product; and for a noninvertible arrow in C the construction does not try to invert F's or G's restriction map. These checks address the size and variance faults most likely to invalidate this statement.

Against delivery-errors B–E: the only node written is the item, so there is no unsplit proof sketch, duplicate node, new false lemma or unrun recorded new-node search. The complete proof stays in the item rather than moving any clause into a helper. All non-elementary imported infrastructure is the cited small-limit statement; all other steps either explicitly construct the objects, prove the identities or use the given coefficient adjunction. There are no SGA references, no route replacement, and no dependencies on the downstream sheaf-tensor results. Imported statements, kind, source and all blueprint metadata remain unchanged except the worker-owned same_as field; the invalid proof-origin place is repaired in the worker-owned field.

## Dry-run validation

The first `deliver.py Q40 det-def-sfb-sheaf-tensor-presheaf --no-push` was terminated with exit code 143 while waiting for the shared worktree allocator, before any preflight output. The second invocation reached preflight but exited 1 on an unrelated shared-DAG parse error:

```
ids: <ROOT>/dag/nodes/sec-smooth-purity/def-cbc-enhanced-diagrams-cones.json does not parse: Extra data: line 187 column 2 (char 30018)
```

A read-only `json.loads` of that file in the shared repository reproduced exactly the same error; the sandbox item parses successfully. That other node is outside this worker's authorized write set, so it has not been edited or replaced. A further dry-run retry was started against the current snapshot. The work is not certified READY without the required OK result.

## Second reading by Q40

I reread the item against `det-def-sfb-sheaf-tensor-presheaf.md` and its proof file in the current `main-20261015` blueprint, and checked all hypotheses, slice variances, and the displayed local and global Hom formulas. Step 1: objectwise tensor, unit, coherence, and naturality agree with clause 1; verdict pass. Step 2: the small representative slice construction uses only essential smallness and small Hom sets and introduces no extra hypothesis; verdict pass. Step 3: the product/equalizer has the correct mixed-variance components, extends wedges independently to every slice object, and uses exactly the cited small-limit universal property; verdict pass. Step 4: restriction along `C/U' → C/U` has the stated contravariant presheaf laws and variance in both variables; verdict pass. Step 5: the coefficient tensor–Hom adjunction gives precisely the local family formula and its wedge naturality; verdict pass. Step 6: the map from a tensor morphism to an internal-Hom morphism has the displayed formula and is natural in the base object; verdict pass. Step 7: the inverse construction, identity-slice evaluation, and naturality in all three variables establish the global bijection; verdict pass.

There are no new nodes to inspect: the only delivered node is the existing item, and its only non-elementary dependency is the existing `lem-coef-grothendieck-small-limits` leaf, whose statement was reopened and matches every cited use. I tested the empty and one-object categories, an arrow category, zero presheaves, and the constant tensor-unit case; all formulas specialize correctly. I found no statement dispute, duplicate, missing citation, SGA route citation, or elementary step that carries a hidden theorem.

Changes made in this second reading: appended this per-step audit and explicit edge-case checks; no node statement, proof step, citation, or dependency was changed. The delivery dry run was retried; the shared worktree allocator was still busy, so I am retrying with the delivery tool until it reports its mechanical result.
