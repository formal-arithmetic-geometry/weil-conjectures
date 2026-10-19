# Stage-1 report: lem-sfb-dc-proper-pushforward-left-adjoint-oe

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dc-proper-pushforward-left-adjoint-oe.json`: four proof steps; the original statement is unchanged. No new nodes; no Mathlib leaves.
- `citations.json`: ten entries, one for each step/node citation, copied verbatim from the cited statements.
- `report.md`: this report.

## Attachments

None. I searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id and blueprint tag and for proper pushforward/adjoint terminology. The closest upper-shriek declarations in `SixFunctors/Etale/Derived/UpperShriek.lean` concern unbounded étale categories and assume a left-adjoint instance; the finite-coefficient instance there has `sorry`. The adic lower-star file concerns finiteness, not an exceptional right adjoint on the item's condensed constructible category. These do not establish this item. No master-source sorry declaration is used as a finished proof.

## WANTED

None. The proof follows the current blueprint's enclosing unit and cites existing DAG statements. No missing external source is asserted to prove an uncited fact.

## Corrections and blueprint comparison

I replaced the earlier sandbox attempt after opening its citations. `prop-coef-integral-exceptional-adjoint` assumes the global base `k = algebraic closure of F_q`; the present setting explicitly permits an arbitrary field of positive characteristic different from ell. Its hypothesis was not justified. Also, restriction from the completed sheaf to the discrete constant sheaf does not by itself identify the item's condensed category with the other theorem's category. Finally, a lower-shriek definition using a chosen compactification does not license replacing that choice by the identity compactification without a comparison theorem.

The replacement follows the opening sentence of `sk-cor-existence-ii.proof.md`: use `sk-thm-existence` (2)--(4) and the proper comparison, then restrict along full subcategories. Its integral coefficient case is over the same standing field as the item. This realizes the unit's stated route and obeys the route lock. The imported node's prohibited external source attributions were removed from `source.external`, and its torsion-limit proof was replaced; all original import flags and blueprint metadata were retained. No source claim about Bhatt--Scholze supplying this precise adjunction is added.

The proof does not identify a condensed topological ring with its discrete constant sheaf. The definitions `sk-def-sfb-constructible` and `sk-def-sfb-bounded-constructible` use the same modules over the pulled-back condensed coefficient ring: they give the same full bounded constructible category, denoted Dbc and Dcons respectively. `sk-lem-integral-models` supplies the extra equality Dctf = Dbc for integral coefficients. The completed/discrete coefficient comparison nodes from the earlier draft are unnecessary and were removed from the proof dependencies.

## Not duplicates

No new nodes were created. Whole-DAG keyword searches and `tools/blueprint_refs.py search` for `right adjoint`, `proper-pushforward-left-adjoint`, `integral models`, and `existence-ii` found the existing general existence theorem, integral-model lemma, and detailed proper comparison used here. The E and Qlbar proper-adjoint nodes have different coefficients; the unbounded finite-category theorem has different source/target categories. The general existence theorem and detailed restriction lemma include this specialization but are broader statements, not exact duplicates of this coefficient-specific node; `blueprint.same_as` is empty.

## Review by NQ

I read the current `main-20261015` chapter `sec-six-functors-basics/_section.md`, unit `sk-cor-existence-ii/_section.md` and its proof, the item's statement and proof, `sk-thm-existence/_section.md` and its proof, and `sk-cor-existence-ii-restriction.md` and its proof. The newly imported chapter/unit have no corresponding JSON records in the shared `dag/chapters` and `dag/units`; I read their authoritative current markdown instead and changed no binding metadata. I also read the source markdown and DAG statement for the constructible-category definitions, localizing closure, integral-model lemma, setting, and restricted direct image cited in the final proof. There are no new nodes whose statements require a separate source audit.

Step 1 uses `sk-def-sfb-bounded-constructible` for boundedness, constructible cohomology and ambient morphisms, and `sk-def-sfb-constructible` for precisely the same description of Dbc with pulled-back condensed coefficients. These give Dcons = Dbc as full categories without invoking derived completeness as part of the definition. The opening statement of `sk-lem-integral-models` expressly gives Dctf = Dbc in the integral case; that substantive fact is cited rather than marked elementary. Both Z and Y satisfy its standing hypotheses. The finite extension and valuation ring are exactly the item's E and O_E.

Step 2 uses the explicit admissible-coefficient list in `sk-def-localizing-closure`, which includes O_E for finite E/Q_l; this is not an assumption of an ambient exceptional datum on all pro-étale sheaves. `sk-def-sfb-dc-setting` gives separated finite-type k-schemes with char(k) different from ell, with no algebraic-closure or finite-field assumption. `sk-thm-existence` states those same scheme hypotheses, supplies the localizing functor and its right adjoint in clauses (2)--(3), and supplies preservation of Dctf by that right adjoint in clause (4). The latter is indispensable and is not inferred from compactness or Brown alone. All these statements were opened and their used clauses copied into `citations.json`.

Step 3 cites only clause (1) of `det-cor-existence-ii-restriction` for the natural proper comparison on localizing categories. Its statement really identifies the compact-support functor with the restriction of ambient Rp_*, so the proof needs neither a hidden compactification independence claim nor the proof-only assertion of a definition. The identity factorization explains the geometric reason, while the cited clause supplies the comparison with the actual chosen compactification. `def-sfb-dc-lower-star` then identifies the item's displayed functor with the restriction of that ambient pushforward. Properness is used exactly here.

Step 4 uses fullness from `sk-def-localizing-closure` and Step 1, and the adjunction supplied by `sk-thm-existence`. I wrote every Hom identification and explained naturality. The restriction G|C_Y is a functor because preservation was established in Step 2. No preservation of arbitrary compact objects by arbitrary right adjoints is assumed. This last step is elementary: compose the given natural Hom bijection with a natural isomorphism and full-inclusion equalities. Unit and counit can equivalently be restricted from the same adjunction.

I checked delivery-errors B--E against the final files. No new statement-only node, duplicate, clause restatement, or unsupported Mathlib leaf was introduced. Every non-elementary fact is in a cited statement, with a verbatim quote for each citation. The only elementary step is the displayed Hom calculation. The coefficient-model mistake and missing base-field hypothesis of the prior attempt were corrected, and its chosen-compactification shortcut was replaced by a cited comparison. The general existence theorem is expressly cited by this unit; the integral-model equality is recorded as a generic tool use. None of the eight cited nodes has a dependency path back to the item, so no cycle through this item is introduced. Existing inherited cycles elsewhere are left untouched.

For edge cases, the identity proper morphism has identity left and right adjoints under the same Hom formula; an empty source has the zero derived category, zero pushforward and zero right adjoint. Empty target forces empty source. No irreducibility, nonemptiness, smoothness, or algebraic closure was used. The source definitions are full categories on all bounded constructible complexes, and no unannounced derived-completeness or finite-coefficient restriction is added to the item's statement.

Mathlib searches were made only using `msearch.py`, with two semantic phrasings, both semantic services, a corrected Loogle pattern using `CategoryTheory.Functor.IsLeftAdjoint, DerivedCategory`, and source grep. I read the hits: module-sheaf pullback/pushforward adjunctions have the opposite adjunction direction and are underived; `isLeftAdjoint_pushforward_of_isIso` needs additional hypotheses on the functor of sites and is underived; the condensed locally constant adjunction is a different pair of functors. None supplies this constructible proper derived adjunction. The old invalid Loogle query using `CategoryTheory.IsRightAdjoint` is recorded as an invalid query, not evidence of absence. The exact command queries and result summaries are copied from `searches.jsonl` into the item. No Lean file was written and no compiler, Lake, or library build was run.

## Unfinished work

The split is ready for the required dry run and then independent second reading. I will leave the sandbox in the accepted state and will not push it.

## Second reading by NQ

I independently opened the current `main-20261015` item source and the enclosing `sk-cor-existence-ii.proof.md`, then checked the item statement hypothesis by hypothesis: finite (E/\mathbf Q_\ell), its ring of integers, the condensed coefficient, properness, and the exact bounded constructible source and target categories all agree. I tested the identity proper map, an empty source, and the zero object; the asserted adjunction specializes correctly in each case.

Step 1 was checked against `sk-def-sfb-bounded-constructible`, `sk-def-sfb-constructible`, and the opening equality in `sk-lem-integral-models`. Their statements define the same full subcategory for the pulled-back coefficient ring and explicitly give the integral equality used. Step 2 was checked against `sk-def-localizing-closure`, `sk-def-sfb-dc-setting`, and clauses (2)--(4) of `sk-thm-existence`; admissibility of \(\cO_E\), the standing field hypotheses, preservation by both restrictions, and the Brown adjunction are all stated there. Step 3 was checked against clause (1) of `det-cor-existence-ii-restriction` and `def-sfb-dc-lower-star`; the comparison is with the chosen compactification and the definition identifies the displayed restricted pushforward. Step 4 was checked against fullness in `sk-def-localizing-closure` and the adjunction in `sk-thm-existence`; its Hom calculation is a short elementary restriction argument, with naturality explicitly written.

There are no new nodes or Mathlib leaves to audit. I nevertheless checked the existing-node searches and the whole-DAG duplicate search recorded by the worker; no exact Mathlib declaration or duplicate blueprint/DAG node supplies this coefficient-specific proper derived adjunction. `citations.json` has one verbatim statement quote for every non-elementary citation, and the cited statements contain the hypotheses and conclusions attributed to them. No SGA source is cited, no Lean/compiler command was run, and no live project file was changed.

I changed only this report section. The change records the independent source and edge-case checks required for second reading; the node, proof steps, citations, and search log were already correct.
