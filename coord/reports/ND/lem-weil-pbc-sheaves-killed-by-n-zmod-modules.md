# Worker report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sheaves-killed-by-n-zmod-modules.json`: statement, split in five steps; no exact Mathlib match for the full item. Its statement is unchanged. All substantive auxiliary facts are existing Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every direct step citation.
- `searches.jsonl`: actual searches made through the required msearch command; the item's historical search records were retained, with the fresh queries appended.
- `report.md`: this report and self-review.

New nodes: 0. New Mathlib leaves: 0. No Lean files, unit records, shared repository files or launcher files were written.

## Attachments

None. Searched the entire read-only slopmaster2 `WeilConjectures/` source for the blueprint id, the recorded `sheaves_killed_by_n_zmod_modules` name, killed-by-n language, and constantSheaf/ZMod combinations. The tag/name search has no hit. `AlgebraicGeometry/Curve/Reductions.lean:153-158` uses sheaves valued in `ModuleCat (ULift (ZMod r))` and a forgetful functor; that is not a declaration comparing modules over the constant ring sheaf with abelian sheaves, and it does not prove these clauses. The torsion language in `CategoryTheory/Sites/SheafCohomologyTorsion.lean` concerns injectives and acyclicity, not this equivalence. The existing node's stage-2 `lean` record is not a proof in the source checkout and was not treated as an attachment.

## WANTED

None. All literature used is present locally.

## Audit and corrections

The imported node is `unsplit` despite retaining an old proof and review. I read that proof rather than treating its historical review as authorization to skip the task. The statement has no detected error, and every clause is retained. The older eight-step proof factors through underlying-set sheafification and finite products. It is mathematically suitable but unnecessarily duplicates the existing module-sheafification interface. The replacement uses `lem-pc-sites-module-sheafification-interface` (Stacks 03CY) with the identity as the abelian sheafification map. This gives an action on the original underlying abelian sheaf, not just an isomorphic replacement; uniqueness of the compatible action then makes the morphism-factorization argument apply to the given structures on G and G'. The old finite-product comparison is no longer a proof dependency.

The new proof still explicitly proves n-annihilation and the formula for constants, constructs the constant-presheaf module structure from the section groups, and proves fullness, faithfulness, the essential-image claim and lifting of isomorphisms. No clause is moved into a newly created node. The module-sheafification lemma is a generic existing Mathlib leaf, not a restatement of this item.

Read the chapter and `sk-thm-p1` unit records and SETUP's three levels. This auxiliary coefficient identification belongs below the unit's curve-calculation route, through the recorded ancestry to `def-weil-pbc-constructible-complexes`. Read both that ancestor's old blueprint text and the corresponding main-20261015 text under `sec-proetale-coefficients/sk-cor-pe-finite-tor-comparison/`: the clause about sheaves of Lambda_T-modules is the same. Its current path is different, but this delivery preserves the item's maintainer-owned chapter/unit metadata and ancestry. No chapter or unit proof is replaced.

## Existing nodes and blueprint searches

Ran `tools/blueprint_refs.py ancestor` on the item, and blueprint searches for `killed by`, `killed by n`, `Z/n` and `sheafification`; searched the whole DAG by the item wording and the ring-sheafification and ZMod ingredient names. No blueprint-imported node states this entire item. Accordingly `blueprint.same_as` is `[]`, and `from.place` now identifies the ancestor's coefficient-module clause. No new node was necessary.

The DAG already contains `lem-pur-torsion-sheaf-constant-module`: it states the existence/uniqueness and linearity comparison on a general site, with substantially overlapping content. I did not create another node for any of those clauses. It is not used in the replacement proof: the independent short proof uses the more basic generic module-sheafification Mathlib leaf and group-level algebra. The related `lem-weil-pbc-module-sheaf-constant-ring-equivalence` compares two models of module-valued sheaves for an arbitrary coefficient ring; it does not assert the torsion image in abelian sheaves and is not required here.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs to justify. The overlap with the already existing general-site torsion lemma is reported above for maintainer consideration, without changing either node's maintainer fields.

## Review by ND

I checked the sources with the node statements open. In `etale-cohomology.tex`, Tag 03RW (`definition-constructible`) defines constructibility for abelian sheaves and module sheaves, and the proof of Tag 03SC (`theorem-vanishing-affine-curves`) explicitly passes from an abelian sheaf killed by a prime to a sheaf of vector spaces. Neither states this full categorical assertion. Thus the proof is correctly marked agent-written, rather than attributed verbatim to those tags. Its supporting theorem is exactly Tag 03CY (`sites-modules.tex`, `lemma-sheafification-presheaf-modules`): the ring may be a presheaf, both ring and additive module are sheafified, the compatible module structure is unique, and module maps to a sheaf factor uniquely. I read Tag 03CW (`definition-sheaf-modules`) for the meaning of module-sheaf morphisms, Tag 0H7J (`sites.tex`, `example-constant-sheaf`), and Tag 00WH (`proposition-sheafification-adjoint`) for the identity sheafification application. The algebraic-structure discussion in `sites.tex`, `section-sheaves-algebraic-structures` (alpha), (gamma), (epsilon) explains the use with rings and abelian groups.

For step 1, `def-weil-pbc-constant-sheaf` says that the constant sheaf is the sheafification of the constant presheaf; it is not being cited as a theorem about locally constant sections. `def-weil-sheaf-of-modules-category` supplies sectionwise actions compatible with restriction. Clause (3) of `lem-weil-pbc-zmod-module-structure-killed-by-n` says exactly that the integer image in any ring acts by integer multiplication. Since eta is a ring map, the displayed calculation with a=n proves n-annihilation without an extra characteristic assumption on T. These are the three direct citations in step 1.

For step 2, clauses (1) and (4) of the ZMod node give the actions on F(U) and linearity of the additive restrictions. The proof writes the resulting presheaf explicitly, rather than citing the existing presheaf-module definition for a general presheaf of rings: that definition is stated only when the ring is already a sheaf. The universal property in `def-weil-pbc-sheafification` proves that id_F is a permissible additive sheafification. The cited 03CY interface explicitly allows the ring presheaf P and this choice of additive sheafification, and explicitly supplies compatibility of its action with the original action. All hypotheses are present: P is commutative, O is its ring sheafification, F has compatible sectionwise P-actions and is already an abelian sheaf. This proves existence on the fixed F and the formula for constants.

For step 3, the module-category definition identifies restriction compatibility with naturality of the action, so any competing structure has the sort of action map to which the interface applies. Step 1 makes its restriction to constants the same prescribed action. The uniqueness clause of the cited 03CY interface is therefore applied to the same ring presheaf, the same module presheaf and the same identity sheafification, not to an unrelated chosen isomorphism. Equality of the action gives equality of structures extending the fixed addition. This checks the full uniqueness clause, including module structures not initially assumed to have the stated formula.

For step 4, clause (4) of the ZMod node applies to the restricted P-modules from step 1 and says precisely that each additive component of phi is linear. The factorization sentence of the 03CY interface applies to this presheaf-module morphism with target G'. Uniqueness from step 3 identifies the source module structure with the original G; because the unit is the identity, the underlying extension equals phi itself. This is fullness over the sheaf of rings, not merely linearity over the constant ring of global constants. The resulting componentwise linearity is exactly assertion (3).

For step 5, the module-category definition identifies morphisms as additive maps with a linearity property, so faithfulness is immediate. Fullness, the image and the inverse-isomorphism calculation follow in a few lines from the preceding established steps. I marked only this final categorical bookkeeping step elementary. No new substantive fact is used there.

I checked the edge cases explicitly. For n=1 a killed sheaf is zero on every object, so the unital zero-ring module is unique and the morphism assertions hold. The zero sheaf works for every positive n. On the empty scheme the sheaf condition forces the expected unique sections, so the constant presheaf need not already be a sheaf and the argument still applies. On disconnected objects the constant ring sheaf can have sections not represented by a single constant; using sheafification of P rather than identifying O(U) with Z/n avoids that false inference. For composite n, neither the group-level construction nor 03CY requires a prime or invertibility in any residue field. No finite type, quasi-compactness, Noetherianity or characteristic condition is silently used.

The fresh leanfinder/loogle/leansearch/grep results were read. `SheafOfModules.fullyFaithfulForget` is about forgetting to presheaves of modules, whereas `toSheaf` forgets to abelian sheaves and the search only supplies faithfulness. Reading `Sheaf.lean:69-92` confirms the distinction. The second natural-language search found generic module sheafification; I read `Presheaf/Sheafify.lean` (construction at 328 and factorization at 364-383) and used its existing DAG interface instead of making a new leaf. The full comparison still needs the sectionwise ZMod construction and the identity-sheafification application, so this item remains a split statement.

Against delivery-errors B--E: there are no new statement-only nodes to leave half-specified, duplicate, or disguise as clauses. Every direct citation is from its statement and has a verbatim quote in citations.json, including the entire action/factorization clause used from the interface. The proof uses no proof-internal construction of another node. The only imported sub-argument over 2000 characters was removed in favor of the existing generic interface; the five replacement steps are all below 1200 characters, and none hides a comparison lemma. Statement, imports, Lean audit and maintainer fields are preserved. The dry run below supplies the independent mechanical acyclicity, route and preflight checks.

## What could not be finished

Nothing mathematical remains in this split. No unproved new node was introduced. Delivery validation is recorded below after the required tool exits.

## Validation

The required `deliver.py ND lem-weil-pbc-sheaves-killed-by-n-zmod-modules --no-push` completed with exit code 0 and printed `OK (not pushed)` at `2efa1531ab`: server preflight passed, including the DAG and split checks. There were no diagnostics requiring a mathematical repair. The dry-run process exited fully before starting the push invocation.
