# Worker report: Q141

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-point-finite-free-sections-tensor.json`: statement, now split into eight steps; Mathlib verdict: no whole-item match. The mathematical statement is unchanged.
- `citations.json`: fourteen verbatim statement excerpts, one for every occurrence of a cited node in a proof step.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log; `write_split.py` is the sandbox-only generation script.

There are zero new nodes and zero new Mathlib leaves. No unit or chapter record changes: this item supplies a subordinate coefficient comparison, not the statement of its unit.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint tag and section/tensor/global-basis terminology. `AlgebraicGeometry.ProEtale.isIso_biproductDesc_sheafExtendScalarsAdjunction_unit` in `SixFunctors/ProEtale/ScalarExtensionFlat.lean` is related but concerns discrete constant ring coefficients. It does not identify completed coefficient global sections or give every clause of this item, so it is not an attachment.

## WANTED

None for this split. All direct sources used here are available. The existing field-completeness node records its own literature history; this split uses that node's stated theorem and does not assert a new completeness result.

## Corrections and scope

The item had no proof. I supplied the point-evaluation calculation, a global basis obtained from the existing adic-basis-limit node, the actual balanced map, its inverse and naturality, exactness, and the chain-map equation. I corrected the source place: Bhatt–Scholze Lemma 4.2.12 is on printed page 30, while Lemma 6.8.2(1) is on pages 58–59. The comparison itself is an agent deduction from their constructions and existing DAG statements, and `proof_origin.by` records that honestly.

The blueprint source read was `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sf-admissible/def-weil-finite-coefficient-point.md`, especially its final stagewise-colimit paragraph. The item's inherited unit is `sk-thm-sf-compatibility`; its coefficient clause is the relevant route. The item remains in its inherited chapter and unit, without a route change. Its `blueprint.from` place specifies the final paragraph and the intermediate scalar-extension comparison.

## Searches and reuse

Read the inherited searches and ran five additional logged searches: LeanFinder with two different phrasings, Loogle, grep of `Algebra/Category/ModuleCat`, and LeanSearch. All services answered. Returned hits concern adic-completion evaluation, module sheafification, finite-generation/presentation, and sections functors, rather than the item's combined completed-coefficient assertion. The exact queries and actual returned names are recorded in `mathlib_searches` and the command's `searches.jsonl`. No unsuccessful service was called a mathematical no-match.

Searched the whole DAG and `blueprint_refs.py` for finite-free and sections/tensor statements. Reused `lem-sfb-local-field-integral-basis`, `lem-pur-adic-basis-limit`, and `lem-pur-proetale-finite-constant-sections`. In particular I did not introduce a second basis lemma or a node restating the comparison. I also read `lem-sfb-finite-free-scalar-coordinates` and the existing completed scalar comparison: their broader categorical formulations are unnecessary for the elementary coordinate calculation written here.

## Not duplicates

No new nodes were created. All candidate helper facts were either existing DAG statements or the elementary finite-sum calculations now written in the proof steps.

## Review by Q141

I read Bhatt–Scholze's Lemma 4.2.12 and its proof (printed page 30), and Definition 6.8.1 and Lemma 6.8.2 with its proof (pages 58–59), using the local PDF. They identify discrete constant sheaves with continuous functions and completed coefficients with the inverse limit of finite quotients. I also read Stacks `sites-modules.tex`, Tag 03EK, label `section-tensor-product`, which defines the presheaf tensor and its sheafification. There are no new nodes requiring additional sources. I checked delivery-errors sections B–E in both copies in that file against the final split.

Step 1 uses the coefficient definition's finite quotient rings, the finite-constant-sections theorem's normalization on constant elements, the definition of completed coefficients, and the sectionwise limit formula. All four statements were opened. The test object is the final object `s`, whose underlying space is one point, so no connectedness or section-surjectivity hypothesis is hidden. The finite constant theorem includes arbitrary objects and is correctly specialized here.

Step 2 uses exactly the existing extending-absolute-value, DVR, and field-completeness statements. I checked that a uniformizer has absolute value strictly between zero and one and that the DVR factorization identifies its powers with the corresponding closed balls. The written Cauchy sequence of residue lifts proves surjectivity; shrinking balls prove injectivity. This supplies the point-evaluation identification without assuming a discrete completed ring or citing a definition as a completeness theorem.

Step 3 uses the integral-basis theorem, whose conclusion gives rank `[L:E]` and integral coefficients, uniqueness of extending absolute values, the DVR factorization, and the adic-basis-limit statement. The last node explicitly gives both the basis columns as compatible residues and the coefficient-map projection formula. Thus it says what the step needs, including its normalization. I checked its hypotheses: the small pro-etale skeleton, a finite integral basis, and `t = u v^e` with `e >= 1`. Compatibility of the absolute values and `|t| < 1` ensure the exponent is positive. The constant section corresponding to a basis element is determined by all its residues, so the resulting basis really is global and agrees with the ordinary integral basis.

Step 4 uses the actual tensor definition and the module-sheafification universal property, both read in full. Its two finite-sum inverse identities and coordinatewise sheaf gluing are written out. It proves that this particular presheaf tensor is already a sheaf, rather than assuming a sectionwise formula for an arbitrary tensor product. No internal-module/ordinary-module equivalence is silently used.

Step 5 checks balancing and extended-scalar linearity before using the tensor universal property, and computes both coordinate maps. Step 6 proves naturality and basis independence on pure tensors, which generate the source. These are elementary calculations from the preceding constructed maps, so no new lemma node is justified.

Step 7 cites the module-sheaf category statement for its precise sectionwise kernel and sheafified-cokernel descriptions. The coordinate kernel and cokernel universal properties explicitly prove exactness of finite powers; restriction of scalars changes neither underlying construction. This verifies both sheaf and ordinary-module exactness, without an unquoted flatness criterion or an unjustified claim that global sections preserves epimorphisms. Step 8 writes the differential equation obtained from naturality and checks the inverses, so the complex comparison imposes no boundedness assumption.

Small cases checked: `E = L` with basis 1 gives the usual unit isomorphism and `e = 1`; a ramified extension uses the `en` cofinal subsequence from the adic-basis statement and does not confuse the two quotient indices. The zero sheaf and torsion module `O_E/(varpi_E)` satisfy the coordinate formulas; no flatness or local freeness of the input sheaf is used. An empty site object gives zero modules on both sides of the coordinate identity. Changing the basis changes only the coordinate proof, because the balanced map has its basis-free formula. Genuine coefficient-field degrees are positive, while every finite-sum argument also handles an empty tuple formally.

Every proof use has a verified verbatim excerpt in `citations.json`. The proof-dependency list is exactly the union of the step uses. Generic coefficient tools are declared in `split_report.tool_uses` for the maintainer's route check. No proof step is longer than 2000 characters; none hides an additional comparison lemma. No statement dispute, unproved new helper, or unfinished mathematical obligation remains in this one-level split.

## Validation

Server-side review and the required full delivery dry run are run using the launcher's prescribed tools. Their final outcomes are recorded below before pushing. No Lean was written or compiled, and no repository or launcher file was changed by this worker.

Validation results: server `review_split` returned PASS with zero new nodes. `deliver.py Q141 lem-weil-point-finite-free-sections-tensor --no-push` exited successfully and printed `OK (not pushed)` at `5efaf03371f`, with server preflight passed. Its only informational note is that the inherited unit has no realization recorded yet; this subordinate item does not own that unit record.
