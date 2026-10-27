# Q34: lem-pod-point-exact-extension-sections

## Files written

- `dag/nodes/sec-six-functors/lem-pod-point-exact-extension-sections.json`: statement node, now split into six steps. The statement and its statement dependencies are unchanged. Mathlib verdict: no exact match for the whole assertion about the specified finite and completed pro-etale point coefficients.
- `citations.json`: fifteen step/node pairs, each quoting the cited statement verbatim.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. The sandbox also holds the search command's original `searches.jsonl` and the local JSON-writing helper. Neither is a project source change.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id, pointExactExtensionSections, completed coefficients, and constant/sections adjunction terminology. The completed coefficient definitions exist, but no sorry-free project declaration states all the present assertions. Generic Mathlib constant-sheaf adjunctions do not prove the specified completed coefficient flatness or exactness of sections on the small pro-etale point site.

## WANTED

None. The imported foundational DVR node already records its own missing standard reference; this item creates no new literature request and uses its statement only.

## Corrections and dependency audit

The imported item had no proof. Its statement is valid as written, including arbitrary modules and arbitrary module sheaves. I supplied the explicit maps rather than identifying the whole ambient topos with modules: Bhatt-Scholze Example 4.2.11 expressly shows that point sections are not conservative on arbitrary sheaves. This split needs exactness only, and does not infer an equivalence of ambient categories.

All statement dependencies remain necessary for the coefficient datum, completed ring, constant module construction and sheaf tensor. No existing node was modified or duplicated. Existing exact sheafification, completed flatness, exact point sections, normalized finite coefficient sections and continuous integral sections supply the non-elementary inputs. Generic tools outside the unit are declared with reasons in `split_report.tool_uses`; no top-level `tool_uses` approval was written. The parent blueprint's second sentence and the unit's point-duality route are unchanged.

The required searches were run through msearch.py, with a second phrasing. Read results for `CategoryTheory.constantSheafΓAdj` (GlobalSections.lean:69), `SheafOfModules.PullbackConstruction.adjunction` (Sheaf/PullbackContinuous.lean:79), `CondensedMod.LocallyConstant.adjunction` and `AdicCompletion.flat_of_isNoetherian` (AdicCompletion/AsTensorProduct.lean:379). The first two give adjunction ingredients, the condensed result has different coefficients/site, and ordinary ring completion flatness does not identify the inverse-limit constant sheaf. None states the whole item by a one-line specialization. New search records match the command log; inherited records were retained. Blueprint searches for constant adjunction, completion flat, exact extension point, and finite constant sections found no exact blueprint duplicate of this combined item.

## What remains

No unresolved stage-1 mathematical subclaim. Existing dependency nodes retain their independent proof obligations; no Lean was written or compiled. Server dry run and delivery outcome are recorded below after execution.

## Review by Q34

I read coord/delivery-errors.md sections B--E in both copies, the chapter and unit records, GOAL.md, the stage-1 brief, and the main-20261015 point-duality proof. The source says that internal Hom at the point is computed over the coefficient ring; this item is its explicit underived extension/sections infrastructure. I read Stacks sites-modules.tex Tag 03EI (`lemma-sheafification-exact`), Tag 093M (`lemma-completion-flat`), the constant-sheaf discussion at Tag 093J, and the sheaf tensor and scalar adjunction discussion adjoining Tag 03EK and Tag 03CY. I read Bhatt-Scholze Lemma 4.2.12 and Example 4.2.11 on printed p. 30 and Definition 6.8.1/Lemma 6.8.2(1) on pp. 58--59. I also read Stacks proetale.tex Tags 0982 and 098H and the existing point-sections node's small-site argument, rather than inferring its small-site statement from the big-site theorem without explanation. No SGA route is used.

Step 1 uses the statement of `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`, which explicitly gives sectionwise exactness and exact sheafification, together with `def-sf-site-constant-module-functor`, which explicitly identifies the underlying abelian sheaf and extended action. A constant exact sequence is sectionwise exact, so there is no finite-generation assumption. This avoids citing the definition of sheafification for the theorem of its exactness.

Step 2 uses the tensor definition for the written unit/multiplication inverses at finite level. I opened `lem-weil-l-adic-extension-integers-dvr`: its statement says PID, so the Noetherian hypothesis follows because every ideal is principal. The statement of `lem-weil-pbc-completed-constant-sheaf-reduction` explicitly says that tensor with the inverse-limit sheaf preserves short exact sequences. Its scheme, Noetherian ring and ideal hypotheses hold for s, O_E and (varpi_E); `def-weil-completed-integral-coefficients` gives exactly the same inverse limit. I use only that node's flatness clause, not an unstated theorem about completion of an arbitrary module.

Step 3 cites `lem-weil-point-proetale-sections-exact`, whose statement gives exact sections for EVERY sheaf of commutative rings on this SMALL site and arbitrary modules over it. Thus it really applies to completed B. Restriction from B(s)-modules to R-modules preserves the underlying kernels and cokernels; that elementary observation is written out. Algebraic closedness is in the fixed datum, and no constructibility enters.

Step 4 opens and uses all four cited statements. The DVR node supplies a finite residue field, the finite-quotient node supplies finiteness of each A_E,n, and `lem-pur-proetale-finite-constant-sections` gives a RING isomorphism normalized on constants, not merely a set bijection. Its X=V=s specialization has singleton underlying space. For the integral ring, `lem-weil-pbc-continuous-coefficients-immersion-restriction` states both the continuous-function sheaf and its inverse-limit identification with the finite constant quotients. The required scheme is Noetherian, checked directly for a field. Its identification is compatible with constants since the projections evaluate constants at every finite quotient. Evaluation on the singleton proves the claimed ring inverse, without identifying a discrete constant O_E sheaf with completed O_E on other objects.

Step 5 uses exactly the universal properties in the four definition statements, all read in full: sheafification; constant module construction with extended action; tensor sheaf as sheafification of presheaf tensor; and linear sheafification. The rule is first extended from the constant PRESHEAF to the constant SHEAF before tensoring, so it is well-defined on all local sections, not only globally constant representatives. The two inverse checks use sheafification uniqueness and B-linearity. I wrote both naturality identities explicitly. These are elementary universal-property manipulations; no uncited general adjunction theorem is required.

Step 6 cites no external fact: it substitutes the already established naturality identities into the chain-map equation, and substitutes the same identities plus additivity into the two-term homotopy equation. Both formulas and the degree indices are written, including the inverse implication. Each degree uses only adjacent terms, so unbounded complexes cause no product or convergence assumption. This is a routine calculation, not a hidden comparison lemma.

For B1--B10, there are no new nodes to carry unsplit proofs, missing hypotheses or duplicate statements; the item's blueprint place is precise and same_as is searched. Recorded searches were actually run. For C1--C8, every non-elementary step uses an existing statement that was opened and checked; quotes are verbatim, no proof-internal construction is cited, and generic off-unit tools are declared. The two elementary steps contain the actual universal-property and homotopy arguments. For D1--D5, no clause was relabelled as a new lemma and no argument was moved into a replacement node. For E1--E7, I checked the flatness Noetherian hypothesis, coefficient normalization, arbitrary-module quantifiers and the actual small site. Edge cases include M=0, F=0, n=1, infinite modules, sheaves with zero point sections, complexes with no boundedness, and the zero sheaf on an empty test object. None invalidates the formulas: no converse from zero point sections is used. All six steps are under 2000 characters (maximum 1377), and each describes one argument.
