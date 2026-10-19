# Stage-1 worker report: lem-coef-strict-intrinsic-right-fibration-slices

## Files written

- dag/nodes/sec-six-functors/lem-coef-strict-intrinsic-right-fibration-slices.json: statement; split in nine steps; no Mathlib match; original statement retained.
- dag/nodes/sec-six-functors/lem-coef-relative-grothendieck-localization.json: statement-only general lemma; unsplit; no Mathlib match. It concerns arbitrary ordinary Grothendieck fibrations with relative fibers, not right fibrations of simplicial sets or the comparison of slices.
- citations.json: 32 step/node quotations copied verbatim from the statements used.
- searches.jsonl: actual search-command records for the item and the new lemma; all services answered. The inherited item searches are retained as well.

## Attachments

None. I searched the project declarations under /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the blueprint tag and by strict/intrinsic, right-fibration and RFib terminology; there were no candidate declarations. The read-only master reference also had no relevant declaration. No Lean file was written or compiled.

## WANTED

WANTED: Chu--Haugseng, Free algebras through Day convolution, arXiv:2006.08269, Proposition 6.2, particularly its final paragraph, for lem-coef-strict-intrinsic-right-fibration-slices. Read online at https://arxiv.org/pdf/2006.08269, printed pp. 12--13; no archive in literature/.

WANTED: Gepner--Haugseng--Nikolaus, Lax colimits and free fibrations in infinity-categories, arXiv:1501.02161, Appendix A, Definitions A.27--A.28, Proposition A.30 and Corollary A.32, for the family comparison. Read online at https://arxiv.org/pdf/1501.02161, pp. 39--41; no archive in literature/.

WANTED: Hinich, Dwyer--Kan localization revisited, arXiv:1311.4128v4, Definition 2.1.1, Proposition 2.1.4 and proof 2.2.2--2.2.6, for lem-coef-relative-grothendieck-localization. Read online at https://arxiv.org/pdf/1311.4128v4, pp. 16--21; no archive in literature/.

WANTED: Lurie, Higher Topos Theory, the isofibration, mapping-core and marked-model foundations cited by the existing technical nodes, for the explicitly reconstructed mapping-fiber argument. No HTT archive is present in literature/; the cited node statements, rather than their proofs, are the interfaces used here.

These are requests for the maintainer to archive the sources; I did not download files or edit the repository's literature list. The item's expanded proof is marked agent-written, since the available local blueprint is agent-written and the external primary sources are online rather than archived.

## Findings and corrections

The item was unsplit, with no proof and no Lean attachment. Its mathematical statement is correct and unchanged. Its higher-naturality clause requires a family localization argument; an objectwise equivalence, even supplemented with comparisons for individual base maps, is insufficient. The new generic theorem supplies exactly that missing operation. The existing statements supply all right-fibration-specific calculations.

The main-20261015 ancestor file is literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md. I read it, the chapter and unit records, and retained the existing historical ancestry and unit binding. This work is below the coefficient-adjunction infrastructure, and does not alter the geometric unit route. The item has no blueprint_update to apply. The two external-unit foundations (enhanced cone calculus and left-fibration equivalence lifting) are declared as generic tools in split_report.tool_uses; no maintainer-owned tool_uses field is installed.

During self-review I corrected doubled TeX escapes in the initially generated raw strings. I also made explicit why the ordinary localization of quasicategories in step 5 is the actual Cat-infinity base, and why the weak equivalences in the fixed-base relative category are exactly the contravariant model weak equivalences. The new lemma distinguishes the marking of cartesian lifts over base weak equivalences from the conclusion that every cartesian lift, over any base arrow, survives as cartesian. Marking all cartesian lifts would give a different total localization.

## Not duplicates

lem-coef-relative-grothendieck-localization vs lem-coef-brown-slice-fraction-calculus: the latter compares one Brown slice localization with a slice over a fixed object; it does not localize a Grothendieck family over a localized base or retain its cartesian transport.

lem-coef-relative-grothendieck-localization vs lem-coef-brown-fibrant-localization-pullbacks: the latter preserves finite limits in one Brown localization; it does not identify the fibers of a localization of a varying relative family.

lem-coef-relative-grothendieck-localization vs lem-coef-cocartesian-straightening: straightening starts with an infinity-categorical fibration; the new input proves that the localization of an ordinary relative Grothendieck fibration supplies such a fibration with the specified fibers. It is not the classification theorem restated.

lem-coef-relative-grothendieck-localization vs lem-coef-enriched-marked-realization: that theorem realizes the degreewise localizations of one enriched category, not a Grothendieck fibration over a base localization.

lem-coef-relative-grothendieck-localization vs lem-coef-strict-intrinsic-right-fibration-slices: the new lemma has neither simplicial right fibrations nor a slice-comparison assertion. Steps 1--4 carry the item's mapping-space and pullback argument; the new lemma only supplies the general family-localization input to steps 7 and 9.

Before creating the node I searched the entire DAG by Grothendieck-fibration, relative-family, Hinich, 2.1.4 and A.30 terminology and the whole blueprint using blueprint_refs search (right fibration, slice, localization, Grothendieck, family), and searched the project Lean sources. The relevant hits were the above general tools and the item itself. No existing node states this family-localization theorem. There are no Stacks tags for these results; I do not assign unrelated tags from ordinary category theory.

## Review by NZ

I read Chu--Haugseng Proposition 6.2 in full, including its strict relative-arrow model and its reference to Hinich, rather than treating the proposition's presheaf classification as a proof of this item. For the new node I read Hinich Definition 2.1.1 and Proposition 2.1.4, and the proof's construction of the fiberwise-localized classifying functor and its comparison of total localizations. Taking opposites gives the cartesian formulation. GHN A.28/A.30 explains the relative Grothendieck construction of the same coherent functor; A.32 is supporting context, not an unproved replacement of the strict/intrinsic comparison. The new node is left statement-only as required.

Step 1 uses the gluing theorem's explicit Kan assertion for relative mapping complexes, the right-fibration-fibers theorem for Kan vertex fibers, the core theorem for equivalences of their edges, and cone calculus for the pointwise equivalence criterion. The marked-point statement identifies Cat-infinity with the nerve of quasicategories enriched in mapping cores. The coherent-nerve statement gives the actual nerve and its naturality, and the slice-arrow statement converts the resulting fixed-target arrow diagram into the intrinsic slice. These statements all have the quasicategory or arbitrary simplicial-base hypotheses needed here. I wrote the enriched natural transformation explicitly; it does not choose a triangle homotopy after the fact.

Step 2 uses the prescribed-target equivalence lift in the left-fibration statement, after opposites. The opposite/isofibration clause in relative-cone-equivalence applies to these quasicategories, so the map really is an isofibration. Exponentiation and the core-fibration theorem then give a Kan fibration on the two actual mapping cores. The path-comparison theorem applies because both cores are Kan and this leg is a Kan fibration. The strict fiber equals the full relative mapping complex by step 1, not merely its set of vertices.

Step 3 uses the cone-calculus statement with shape a point; this is exactly the coherent fixed-target slice. Its statement provides the homotopy-fiber formula, including the triangle. The marked-point and coherent-nerve statements identify both sides with the objects calculated in step 2. The full-essential-image theorem applies after this fully faithful calculation. Essential surjectivity onto the defined intrinsic subcategory is its definition, so no separate node restating that clause was created.

Step 4 uses the horn definition to prove pullback stability and the isofibration-pullback-limit statement to prove the strict square is a categorical pullback. This theorem allows any functor h and empty pullbacks. The formula on a parameter simplex proves naturality on the full enriched fixed-base category. For equivalences of bases I used the quasi-inverse characterization, not a claim that a strict inverse exists. Pullback along its coherent inverse supplies the inverse intrinsic transport. This is enough for descent compatibility, while the construction of the full coherent descent is reserved for steps 7--9.

Step 5 uses the marked-point model and the simplicial-model localization theorem, whose statement explicitly includes localization of the ordinary fibrant subcategory. The equivalence markings are canonical and every functor preserves them. This checks the actual functor from the ordinary category of bases to Cat-infinity, not just an abstract equivalence of their homotopy categories. The source and target universe is enlarged for this category of small quasicategories.

Step 6 opens the right-fibration-fibers and gluing statements for both directions of the fiberwise weak-equivalence criterion. In the converse the inverse homotopies are over D, so their component edges lie in Kan fibers and are equivalences; cone calculus gives the corresponding natural equivalences on total spaces. The right-fibration-presentation statement supplies the actual simplicial contravariant model structure, all objects cofibrant, and its precise enrichment. The model-localization statement supplies localization of its ordinary fibrant objects, including its vertex map and mapping comparison. Pullback preserves relative homotopy inverses, so the required relative functors exist.

Step 7 uses the new generic family-localization statement only after checking all its hypotheses: ordinary Grothendieck lifts by degreewise pullback, weak-equivalence preservation from step 6, and equivalence of localized fibers over every base weak equivalence from step 4. The tuple factorization gives the cartesian universal property and the pullback associators. The weak classes contain isomorphisms and are closed under composition; their saturated versions have the same localizations.

Step 8 uses the Cat-infinity limits statement for existence of pullbacks and the arrow-target theorem for cartesian evaluation, its edge criterion, and its coherent slice transport. The class of arrows equivalent to strict right fibrations is pullback-stable by step 4. Restricting to this full subcategory preserves the cartesian universal property because the testing mapping spaces are unchanged. Thus its fiber is the whole intrinsic right-fibration slice, not merely a category of strict triangles.

Step 9 checks that both components of every marked total arrow are equivalences, by factoring it into its vertical weak map and its cartesian lift over a base equivalence. Cone calculus's pointwise criterion makes its arrow-category image an equivalence. The new theorem supplies total localization, its full functor-category universal property and preservation of cartesian lifts. The resulting comparison is a map of cartesian families whose fibers are the already constructed J_D. Opposite cocartesian straightening supplies the coherent transformation on the localized base; cone calculus's pointwise criterion makes it an equivalence. This is why arbitrary coherent transformations and higher base simplices are included. No proof of a cited node, or presheaf classifier as a substitute for this family argument, is used.

Small cases: for D empty there is only the empty right fibration, and both categories are terminal. For D a point this is the inclusion of Kan complexes into Cat-infinity over a point, with the actual Kan mapping complexes. Empty fibers and even empty mapping spaces are allowed throughout: the Kan and path-fiber theorems impose no nonemptiness. The example empty total space over a nonempty base is retained; it does not make an invalid assertion that all fibers are inhabited. Identity and composite base maps act by identity and tuple reassociation on strict pullbacks, with the family localization supplying all higher coherence. All total constructions remain in U for fixed U-small bases; their collections and functor categories are formed in containing universes.

I checked delivery-errors B--E against the files: the new node has a standalone statement, definitions or explicit meanings for its notions, a precise source and blueprint place, real recorded searches, and no proof; no Mathlib hit is an exact match. All non-elementary claims in the item have node citations, and every citation has a verbatim statement quotation in citations.json. I checked the dependency closures for a return path to this item; none was found. There is no relabeling of one clause as a child node, no unstarted induction and no source error requiring a statement correction. Every proof step is shorter than 2,000 characters; there is no long step hiding a separately stated comparison. All sources in the proof are on the permitted route.

## What remains

The general family-localization lemma is intentionally unsplit: it is the one new next-level task. There are no outstanding repairs to this item's split. The independent second reader must read the split and sources and deliver it; this worker only runs the required no-push dry run.
