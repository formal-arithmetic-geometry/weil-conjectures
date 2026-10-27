# Stage-1 delivery: lem-zl-finite-rational-heart-comparison

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-zl-finite-rational-heart-comparison.json: existing statement, split into seven proof steps; Mathlib searches find no exact match.
- citations.json: 17 entries, one verbatim statement quotation for every step/node citation.
- searches.jsonl: actual msearch.py results retained without edits.
- report.md: this report.

No new nodes; no Mathlib leaves created. The statement and all statement dependencies are unchanged.

## Attachments

None. Searched the live lean/WeilConjectures tree for the blueprint id, rational/finite/heart terminology, and finite direct-image declarations. Read DeligneLaumon/Reduction/FiniteDirectImage.lean: its finished results concern purity/reality of Weil direct images, not this item's integral-category identification and specified rational fibre maps. No exact complete project declaration was found.

## WANTED

None. The mathematical source documents used are available locally.

## Findings and changes

The imported item had no proof. Identifying the two integral categories cannot be inferred merely from the two definition nodes: the proper-base-change definition explicitly includes uniform local models and compatible etale-origin witnesses. The existing lem-weil-pbc-integral-stratified-perfect-characterization states precisely the additional comparison, including the smooth-purity category and the same completed coefficients and reductions. Reusing it avoids a duplicate comparison node and avoids treating the required witnesses as definitional.

Bhatt–Scholze Proposition 6.8.14(2) supplies the raw rationalization context, not the complete finite-morphism stalk argument. The proof therefore transports the integral functor and isomorphisms that are hypotheses, rather than claiming this proposition constructs them. Exactness on the heart is proved from distinguished triangles. Completed pullbacks are compared through the existing projection-normalized bridge before invoking their existing bound-preservation theorem. Point sections are taken only after the derived comparison, never interchanged with a general inverse limit.

No statement dispute or change of the blueprint/unit route was necessary. The common ancestor is lem-zl-finite-pushforward, through lem-zl-finite-adic-direct-image. The item realizes the rational exactness and finite-stalk interpretation needed by the ancestor proof's first two sentences. Chapter and unit records are untouched.

## Mathlib and duplicate searches

Read the results of all four fresh searches recorded in searches.jsonl: LeanFinder for raw rationalization and fibre sections; Loogle for IsLocalization and IsTriangulated; grep for rationalization, localized t-structures and pro-etale sections; and a second natural-language phrasing in LeanSearch for uniformizer inversion and exact hearts. The semantic hits give abstract localization lifts, algebraic adic-completion exactness and condensed-module constructions, not this project-specific comparison. The existing item's five earlier search records are preserved. No unsuccessful service was recorded as an absence.

Searched the whole DAG by rational/heart/localization/point-section terminology and by the simultaneous occurrence of both integral-category definition ids. Searched the whole blueprint using blueprint_refs.py for rational heart, rational transport, localized tstructure, finite rational, stratified perfect, integral stratified, point proetale sections, finite fibre and finite direct image; read the matching finite-morphism nodes. The broader characterization, localization and pullback nodes already exist. No new node is needed and no new same-tag pair needs distinguishing.

## Not duplicates

No new nodes. The reused nodes remain unchanged.

## Review by O1

I read the current item and its parent lem-zl-finite-adic-direct-image, the ancestor's main-20261015 proof, the chapter and unit records, and the three blueprint levels in SETUP.md. I read Bhatt–Scholze Proposition 6.8.11(3), Proposition 6.8.14(2) with its proof, Remark 6.8.15 and Lemma 6.5.9(4)-(5), together with the discussion leading to Proposition 6.6.11. These distinguish derived comparisons from degreewise consequences and show why rationalization itself does not require a Karoubi envelope. For the point-section input I read Stacks proetale.tex, lemma-w-local-strictly-henselian-extremally-disconnected (0982) and lemma-w-contractible-is-weakly-contractible (098H), including the local-lift proof of surjectivity on sections. I also read algebra.tex, lemma-flat-localization, for comparison with the explicit fraction calculation written in step 6. There are no new-node sources to review.

For step 1 I opened lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, and lem-weil-pbc-integral-stratified-perfect-characterization. The first two give exactly noetherianity and finite dimension for finite-type schemes over a field. The third explicitly compares both project categories, retaining the uniform models and compatible witnesses, and states equality with the same ring and reductions. I checked its hypotheses on X,Y,s and on S by the displayed finite-algebra tensor-generator argument. Invertibility of ell follows from ell differing from the characteristic. The empty scheme is allowed throughout.

For step 2 I read both rationalization definitions, the standard-pair definition, and prop-weil-localized-tstructure. Both definitions expressly keep the same objects and tensor the same Hom modules, with no idempotents adjoined. The proposition supplies t-exact localization and essential-image integral-heart representatives; these are claims of its statement, not extrapolations from its proof. This avoids assuming that an arbitrary integral representative of a rational heart object is already concentrated in degree zero.

For step 3 I read prop-weil-pbc-rational-transport and def-weil-derived-direct-image. The former extends supplied exact linear functors and actual natural transformations; the latter prescribes the rational extension of the integral tower image. The integral comparison is a hypothesis of this item. The proof preserves beta and rho and their inverses by componentwise localization. It does not infer equality of integral maps solely from equality of projections.

For step 4 I read clause (4) of lem-weil-heart-short-exact-triangles. It states both directions of the heart/triangle criterion. The preservation of both rational halves is proved directly using their integral representatives and the hypothesis on T, so applying the criterion really establishes exactness of the heart functor.

For step 5 I read the full statements of lem-a1-integral-pullback-completed-comparison and lem-per-integral-pullback-bounds. The first relates the specific two pullback models with their actual projections and shifts. The second gives constructibility and preservation of both integral cohomological bounds without a false flatness assumption on the completed ring map. Step 1 verifies all its scheme hypotheses; it applies separately to y,v and each x. Its stated empty-scheme clause covers the empty fibre.

For step 6 I read lem-weil-point-proetale-sections-exact, item (3) of def-weil-finite-coefficient-point, and lem-weil-l-adic-integers-localization-uniformizer. They give exact termwise sections, the actual rational point functor, and E=O_E[1/varpi]. Finite biproduct preservation follows from the inclusion/projection identities. The additional tensor/cohomology assertion is proved in the step by the denominator-and-cycle argument; it is not left as an uncited flatness assertion. At a torsion lattice localization kills the torsion as this argument predicts; for a zero complex and empty biproduct all maps are zero. Integral torsion heart objects are permitted: their reductions may have degree -1 Tor, and the proof never assumes otherwise.

For step 7 I opened def-weil-local-frobenius-trace and def-weil-ordinary-compact-cohomology. The former defines a stalk as degree zero of the point fibre after completed pullback, and the latter defines ordinary cohomology using the structure direct image to s. Since h is precisely that structure map, the middle term is the asserted H^0(S,F_S). Naturality is checked for integral morphisms and then for fractions, rather than simply claiming it transports; the actual localized beta and rho supply the restriction arrows. Conjugating naturality squares by an integral-heart representative proves independence of that representative.

I checked delivery-errors B–E against these files: no statement-only child carries a hidden proof (there are no children), every non-elementary fact is either a cited statement or a supplied hypothesis, no definition is asked to prove a comparison, no cited statement is strengthened, and no cycle reaches the item through any of the cited dependencies. Every proof step is below 2000 characters. citations.json contains a verbatim quotation of each used statement; all 17 match the current shared DAG. The generic off-unit mathematical tools are declared in split_report.tool_uses with their precise purpose; this does not replace any finite-morphism route step.

## Unfinished work

None in the stage-1 split. Existing cited unsplit nodes retain their own queued work. Required server dry run and delivery are performed after this report is written.
