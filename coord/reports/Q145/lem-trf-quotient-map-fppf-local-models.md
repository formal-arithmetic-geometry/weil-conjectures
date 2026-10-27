# Stage-1 report: lem-trf-quotient-map-fppf-local-models

1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-quotient-map-fppf-local-models.json`: statement, now split into four steps; its statement and statement dependencies are unchanged. Mathlib searches found related declarations but no exact or one-line match.
- No new node is delivered after repair. The already-landed `lem-trf-fppf-covering-is-fpqc` supplies the Mathlib leaf `AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`, Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:66-69. The former conflicting sandbox copy is retained only as `prior-delivery-leaf.json`, outside the delivery node directory.
- `citations.json`: verbatim statement quotes for all seven step citations.
- `searches.jsonl`: actual searches recorded by msearch.py; the item's inherited search records were retained and the current searches appended.
- `report.md`: this report and signed self-review.

2. Attachments

None. I searched `lean/WeilConjectures/` for the item tag and for quotient sheaves, equivalence relations, etale relations and their pullbacks. No project declaration states every clause of the item. The existing kernel-pair declaration is only an ingredient; Mathlib's covering inclusion is delivered as a leaf, not an attachment. No Lean was written or compiled.

3. WANTED

None. All sources used are in the read-only repository.

4. What was wrong or missing

The item had a statement and searches but no proof. Its Stacks source reverses the roles of s and t relative to the item: I explicitly use the pair (a_i g,u), hence s r=a_i g and u=t r. There is no statement error and no hypothesis was added or removed. In particular U need not be affine here, because separatedness and local quasi-finiteness of s are already explicit assumptions. The source's further effective descent and global representability are outside this item's conclusion.

The sheaf condition needs descent of maps into U. The existing `lem-weil-pbc-fpqc-representable-descent` only accepts fpqc coverings; `def-pc-fppf-site` alone does not supply that implication. The initial delivery therefore added the exact Mathlib leaf for the fppf-to-fpqc covering inclusion. The returned-landing repair reuses the same leaf now landed by another item. I did not cite a definition as a theorem. The existing etale-only covering lemma does not cover arbitrary fppf covers.

The previous delivery and its report, proof, citations and search log were retained. At this repair continuation no delivery process for this item was active. The required initial dry run reproduced the returned collision: a node other than the item would be modified. That dry run exited before any repair or further delivery invocation.

5. What could not be finished

Nothing mathematical remains in this one-level split. The only former new node is now reused from the live DAG as a Mathlib leaf, with no deferred proof. Server dry-run and push results are recorded below after they finish.

## Sources and searches

I read the current blueprint's `sec-trace-formula/sk-i-curve-zero/_section.md` and `lem-trf-local-term-locality.md`, the chapter and unit records, and the existing item's ancestry through `lem-trf-etale-affine-quotient-representable`. The item supplies the local-model subargument of the existing quotient-presentation route; no chapter or unit step is replaced. `blueprint_refs.py ancestor` gives `lem-trf-local-term-locality`; the leaf prepends this item to the inherited via chain.

The proof follows Spaces Tag 0265 (`lemma-presentation-quasi-compact`), first representability step, from local lifts through its displayed pullback formula. I also read Sites Tag 00WK (`lemma-sections-sheafification`), Groupoids Tag 045Y (`lemma-quotient-pre-equivalence`), Descent Tag 023Q (`lemma-fpqc-universal-effective-epimorphisms`), and the equivalent relative functor-of-points assertion in Etale Cohomology Tag 03O3. For the last step I read Schemes Tag 01KU (`lemma-separated-permanence`), item (3), and Morphisms Tag 01TM (`lemma-base-change-quasi-finite`), item (2).

For the new leaf I read the entire statement and proof of Topologies Tag 022C (`lemma-zariski-etale-smooth-syntomic-fppf-fpqc`) and Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:58-98, especially the exact precoverage inclusion at lines 66-69. The proof checks the second fpqc condition by taking a finite subcover of affine-open images of the fppf maps, which are open. This is not an assumption that every covering arrow is quasi-compact.

Before creating the leaf I searched the whole DAG by 022C, the lemma label, fppf/fpqc keywords, and the Mathlib declaration name, and read the potentially overlapping statements. I searched the blueprint with `subcanonical`, `fpqc morphisms`, `fppf fpqc`, `022C`, `fppf covering`, `local representatives quotient`, `kernel pair`, `separated locally quasi-finite` and `local models`. No blueprint node states the leaf or this item in another form, so both same_as fields are empty. I also searched the project Lean for the covering inclusion; its occurrences only apply the Mathlib theorem in more specific arguments.

The leaf's semantic searches returned generic cover/precoverage APIs. Loogle returned the exact precoverage inclusion, and the required msearch grep located its file and line. I opened that declaration and read its proof. The preliminary Loogle query returned the weaker topology inclusion, which I recorded as related; it was not used to claim a statement about covering families. All recorded current queries are exactly those in searches.jsonl. The item's two semantic phrasings returned etale pullbacks, open-chart local representability, spreading-out and local-section declarations, not quotient-sheaf local models. I read the relevant Mathlib representability and effective-epimorphism source: the first assumes relatively representable open charts in the Zariski topology, and the second descends maps along a scheme morphism; neither is this item.

## Review by Q145

I checked delivery-errors B to E with the JSON statements and the sources open. The new statement introduces T, the covering family and the universe convention explicitly, cites its four notions, has no proof sketch or proof dependencies, and is marked mathlib with the declaration, file and line actually read. It is a general covering theorem needed to apply an existing descent theorem, rather than a clause of the local-model item.

For step 1 I reread `lem-weil-pbc-fpqc-representable-descent`: it gives unique gluing of maps into any scheme X for an fpqc family. The existing covering leaf supplies exactly that hypothesis; in this repair I reread its current statement, including the finite affine-open clause, and replaced its quote with that current verbatim statement. A covering over T has the same underlying fppf maps when viewed over S. Applying the descent statement to targets U and S ensures the glued map is an S-map. The sheaf equalizer clause in `def-weil-pbc-sites-and-cohomology` then checks the defining equality q(u)=a|_W after that cover. This is a direct subtype gluing proof; no representability descent or scheme effective-descent theorem is hidden in it.

For step 2 I reread the first local-representation clause of `lem-weil-pbc-site-sheafification-sections-local`. It applies to P(W)=U(W)/R(W), whose sheafification is F by the item. I checked that the item's size convention permits set values containing the site's objects and arrows, as the cited statement requires. Naturality evaluated at id_T explicitly identifies the transformation a with a section, and choosing a representative of each quotient class produces the a_i. No full Yoneda lemma is assumed under a citation only asserting full faithfulness.

For step 3 I reread `lem-trf-etale-relation-kernel-pair` in full. Its statement gives the canonical isomorphism h_R -> h_U times_F h_U for a monomorphic equivalence relation on every test scheme; the item has all these hypotheses. Its statement does not require affine U or separated projections. Evaluating its bijection at (a_i g,u) gives a unique r with s r=a_i g and t r=u. `def-pc-fibre-product` states existence and the universal property for arbitrary scheme pullbacks, so this is exactly the T_i-points of X_i. The displayed inverse maps and uniqueness prove naturality and the specified map to U. The step only substitutes one coordinate in the cited kernel-pair bijection; it does not assume a new local-model lemma.

For step 4 I reread both clauses of `lem-weil-pbc-separated-lqf-base-change`. The projection is exactly the base change of s along a_i, so both explicit assumptions on s apply. The generic off-unit permanence theorem is declared in split_report.tool_uses; it is a tool used on the source's route. No permanence property is taken from a definition node.

I tested diagonal relations (X_i=T_i and the bijection is the unique lift), the total relation over a point (X_i=T_i times U with u=t r), and empty schemes. If T is empty, the empty cover is permitted and the sheaf has its required unique empty section. If U is empty and T is nonempty, a map h_T -> F does not exist, so the quantified lifting assertion is vacuous. Infinite covering families are allowed, and the proof imposes no finite cover or quasi-compact arrow assumption. Nonseparated U causes no problem: only the assumed property of s and its base changes is used. No proof step exceeds 2000 characters. All cited uses occur in proof_deps, and citations.json copies the cited statements verbatim; no citation relies on the proof of a node or on a tag without the corresponding node.

## Not duplicates

lem-trf-fppf-covering-is-fpqc vs lem-trf-space-closed-immersion-cover-descent: the existing statement descends closed immersions of algebraic spaces along etale charts; it does not assert inclusion of arbitrary fppf covering families in fpqc coverings.

lem-trf-fppf-covering-is-fpqc vs lem-trf-fppf-local-open-subfunctor-descent: the existing statement descends a locally represented open subfunctor; it assumes sheaves and local lifts, and does not state the covering-topology inclusion.

lem-trf-fppf-covering-is-fpqc vs lem-weil-pbc-finite-locally-free-degree-etale-descent: the existing statement descends finite local freeness along etale covers; it does not assert that general fppf covers are fpqc.

lem-trf-fppf-covering-is-fpqc vs lem-weil-pbc-etale-covering-affine-refinement: the existing statement gives a finite affine refinement of an etale cover of an affine scheme; the leaf applies to arbitrary fppf covers of arbitrary schemes.

lem-trf-fppf-covering-is-fpqc vs lem-weil-pbc-fpqc-finer-than-etale: the existing statement only concerns covers in a small etale site, whereas this leaf includes all flat locally finitely presented jointly surjective families, without etaleness.

lem-trf-fppf-covering-is-fpqc vs lem-galois-fpqc-descending-types-morphisms: the existing statement is an effectivity theorem for scheme descent data satisfying three hypotheses on a morphism property; it does not assert the fppf/fpqc covering inclusion.

lem-trf-fppf-covering-is-fpqc vs lem-trf-fppf-family-coproduct-descent-encoding: that statement concerns a singleton covering from a coproduct together with descent-data equivalence; this leaf directly concerns the original family and has no descent datum or coproduct hypothesis.

lem-trf-fppf-covering-is-fpqc vs lem-trf-fppf-affine-refinement-pullback-model: that statement constructs affine refinements and pulls back a fixed descent datum; this leaf states inclusion for the original family without auxiliary data.

## Validation

The required deliver.py --no-push completed with exit code 0: `OK (not pushed) deliver/Q145/lem-trf-quotient-map-fppf-local-models at 2dce6326c55: preflight passed`. The delivery tool ran the server preflight; no DAG or split check was run locally. The dry run exited before the push invocation.

## Repair of returned landing

The return reported that `lem-trf-fppf-covering-is-fpqc` had already been created for `lem-trf-open-sheaf-coproduct-base-change`. The initial required dry run confirmed that the retained sandbox would modify that other node. I compared the retained leaf with the live node: both assert the same covering-family inclusion and identify the same Mathlib declaration. The live node additionally spells out the finite affine-open consequence of the fpqc definition. It supplies every fact used in step 1. Renaming our copy would create a duplicate of that existing statement, contrary to the stage-1 duplicate rule, so I removed the colliding copy from the delivery and reused the existing id. Its prior contents are archived only outside `dag/nodes/`; the original search log is unchanged. There are now zero new nodes and zero new Mathlib leaves.

I reread all seven current cited node statements: the covering inclusion, descent of scheme morphisms, the sheaf equalizer definition, local sections of sheafification, the equivalence-relation kernel pair, the fibre-product universal property, and separated/local-quasi-finite base-change permanence. The six other citation quotes still occur verbatim; only the covering-inclusion quote changed. I rechecked Spaces Tag 0265 (`lemma-presentation-quasi-compact`) and Topologies Tag 022C (`lemma-zariski-etale-smooth-syntomic-fppf-fpqc`) with Mathlib Fpqc.lean:66-69. The use of s instead of t remains the explicit interchange already reviewed: the pair is (a_i g,u), so s r=a_i g and u=t r. No statement or hypothesis changed. Empty targets and infinite covering families still satisfy the cited covering theorem, and no quasi-compactness assumption on individual covering arrows was introduced. The item is unsplit on the current live DAG; its live statement is identical to the retained one. The delivery tool rebuilds the commit over current `sheaf-dag`, retaining live maintainer metadata.

The old validation commit recorded above belongs to the returned delivery. The new repair must pass a fresh server dry run before pushing.
