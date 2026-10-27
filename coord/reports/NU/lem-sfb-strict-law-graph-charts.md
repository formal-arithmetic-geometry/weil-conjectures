# Stage-1 delivery: lem-sfb-strict-law-graph-charts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-strict-law-graph-charts.json: item, statement unchanged, seven proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-quasifinite-normal-dense-open-immersion.json: statement-only general normal-target birational monomorphism criterion; unsplit, no Mathlib match.
- citations.json: verbatim statement excerpts (whole statements) for every proof-step citation.

## Attachments

None. Searched lean/WeilConjectures for the item id, strict birational laws, group chunks and birational graphs. No project declaration states the item. No Lean files written, compiler invoked, or repository git commands run.

## Literature

WANTED: Bosch--Lutkebohmert--Raynaud, Neron Models, local PDF literature/bosch-lutkebohmert-raynaud-neron-models.pdf, 5.3 Lemmas 1--3, printed pp.120--121, for lem-sfb-strict-law-graph-charts. The primary scan https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf was read online at PDF pages 125--127, including 5.2 Lemma 4 at PDF page 124. The local file is absent, so proof_origin is agent under the worker brief; no literature file was downloaded or written.

Read local Stacks more-morphisms.tex, lemma-quasi-finite-separated-quasi-affine (02LR) and lemma-quasi-finite-separated-pass-through-finite (05K0); morphisms.tex, lemma-monomorphism-loc-finite-type-loc-quasi-finite (0CT8) and lemma-finite-birational-over-normal (0AB1), checking tags against tags/tags. These supply the general criterion's source. The proposed new node is not a disguised strict-law clause: it has no law, graph, division or translation hypotheses and is a general scheme theorem.

## Issues found and corrected

No statement dispute. The schematic graph closure initially requires care, but BLR's statement really is about the closure, not merely a chosen open graph. BLR first establishes the identity on the closure by schematic density; applying translation cancellation only on the original graph would not suffice. The proof now spells out this point. It does not claim schematic density survives arbitrary T -> Gamma; the equality is established on Gamma first and only then pulled back. Associativity stated as equality of rational maps is upgraded to equality on the common domain using reducedness and the closed equalizer. This handles the source's stronger convention.

Blueprint search: blueprint_refs ancestor returns None; retain the inherited null ancestor and via list. Searches of the full DAG and blueprint for birational law, birational monomorphism, quasi-finite birational, quasi-finite normal, schematically dense, dense open immersion, and Zariski found no node stating the new general criterion or the item. Read the latest six-functors-basics chapter and sk-thm-sf-ctf-stability unit; this BLR prerequisite is below its route. Neither the unit nor chapter is changed.

Mathlib: all new searches ran through msearch.py and are in searches.jsonl. Read the returned hits. In particular Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:358--359 only gives an open immersion into the relative normalization; the target-identification is a further theorem. FlatMono's theorem assumes flatness, absent from the new criterion. The semantic searches were repeated with a second phrasing. Unknown IsNormal/NormalScheme identifier queries are recorded as the actual zero-hit/error responses, not evidence by themselves. The later substring Loogle query finds the normalization theorem, and the source grep confirms its lines. No Mathlib leaf is claimed.

## Not duplicates

lem-sfb-quasifinite-normal-dense-open-immersion vs lem-sbc-normalization-dense-open: existing statement identifies normalization in a dense open; it does not give the quasi-finite monomorphism/open-immersion criterion for an arbitrary reduced source.
lem-sfb-quasifinite-normal-dense-open-immersion vs lem-sbc-normal-dense-open-integral-section: existing statement extends integral functions from a dense open; it does not assert a scheme morphism is an open immersion.
lem-sfb-quasifinite-normal-dense-open-immersion vs pqf-lem-normalization-open: existing statement embeds a separated quasi-finite scheme into its relative normalization, not directly into the given normal target; our hypotheses must also imply quasi-finiteness and identify the normalization.
lem-sfb-quasifinite-normal-dense-open-immersion vs thm-pqf-immersion-descent: existing statement approximates the relative normalization factorization by finite schemes and has no normal-target identification.
lem-sfb-quasifinite-normal-dense-open-immersion vs thm-pqf-zmt-factorization: existing statement factors a separated quasi-finite map through an unspecified finite scheme; it does not identify that scheme with a normal target.
lem-sfb-quasifinite-normal-dense-open-immersion vs det-wrp-cover-open-immersion: existing statement treats connected etale covers of a normal variety and an immersion into their normalization; ours allows a non-etale monomorphism and a general normal Noetherian target.
lem-sfb-quasifinite-normal-dense-open-immersion vs lem-trf-finite-birational-normal-iso: existing statement requires a finite map and integral source and target, rather than a finite-type monomorphism that need not be finite.
lem-sfb-quasifinite-normal-dense-open-immersion vs lem-trf-integral-birational-normal-isomorphism: existing statement requires an integral map between integral schemes. Our source can be disconnected and our map is typically an open immersion that is not integral.
lem-sfb-quasifinite-normal-dense-open-immersion vs lem-trf-proper-birational-normal-curve-iso: existing statement requires proper maps of integral curves over a field. Ours assumes neither properness nor dimension one nor a field base.
lem-sfb-quasifinite-normal-dense-open-immersion vs lem-sfb-finite-normal-generic-section-extension: existing statement extends a section of a finite morphism; ours starts with an arbitrary reduced-source monomorphism and proves it open.

Also read the same-law neighbours: strict-law-base-change, translation-embedding, relative-rational-flat-regularity, and complete-square-group. None is the new general criterion; the last is a user of this item and is never cited, avoiding a cycle. The already-present normal-modification criteria require properness and cannot apply here. The item has no newly created nodes restating its individual clauses.

## Review by NU

I read BLR's actual graph-closure proof (5.3 Lemmas 1--3 and its division paragraph) in the primary scan. Its generic variable is w with (y,w), (z,w), (x,yw) in D. Step 2 proves the needed density from D_y -> V_y and the dense D_x, then intersects D_z; this works component by component without assuming geometric connectedness. Residue extensions use the exact base-change node, whose statement explicitly preserves every strictness witness for arbitrary base change.

Step 1 uses smooth base change, smooth ascent of normality, finite-type composition/base change and the finite-type Noetherian algebra lemma. I opened every cited statement. The induction Y^n -> Y^(n-1) needs no separate smooth-composition theorem. Normality gives reducedness directly because its stalks are domains. The graph is a pullback of the closed diagonal; on affine charts the closure's kernel ideal makes the open graph schematically dense, which also proves the closure reduced. No assertion of normality of Gamma is needed.

Step 3 uses the reduced dense-image lemma to extend rational associativity across its common open domain, then the smooth-flat lemma and dense-flat-pullback lemma to extend the identity from G times Y to Gamma times Y. Both source inclusions are quasi-compact and quasi-separated: all schemes here are Noetherian, and G is an open subscheme of the separated finite-type closure. The pullback is flat because it is a base change of Y -> S; the quoted smooth base-change and smooth-flat statements say exactly this. The closed equalizer uses the definition of a closed diagonal, with its ideal zero on a schematically dense open. This argument is scheme-theoretic, so it applies before any nonreduced test scheme is chosen.

Step 4 uses exactly the injectivity for every T asserted by translation-embedding; after step 3, any two graph coordinates determine the third by group cancellation. Step 5 checks the new criterion's full hypotheses: finite type via the finite-type-to-separated-target statement, reduced source from step 1, normal Noetherian target, monomorphisms from step 4, and matching dense opens D,V,W with source G. I explicitly checked that a section of a monomorphism is inverse, giving the full inverse images of V and W rather than only a set-theoretic identification.

Step 6 uses the reduced dense-image statement once more: a representative's graph factors through the closure because its closed-ideal pullback vanishes on the dense overlap. The same proof is written for division, with coordinates (x,r(x,z),z); multiplication regularity alone would not justify maximality of division. Step 7 gives each variable case separately: coordinate pairs 12/13, 12/23 and 13/23. It uses only the proven open charts, the exact fibre-density/base-change statement and group cancellation from the translation node. All quotes in citations.json were copied from the files actually read.

For the new criterion I checked the normal-target Zariski Main argument: a finite-type monomorphism is separated quasi-finite (0CT8), and 02LR embeds it into relative normalization. Locally on a normal target component the source is reduced and has one dense isomorphic open, so its relative integral closure is the normal target ring; integrality inside its fraction field gives the identification. Empty components are handled by the dense-open hypothesis. This is a genuine further lemma, left statement-only for its own split. Small tests include the identity, a proper dense open immersion, disconnected normal targets, and empty schemes. Removing density of the source allows an extra closed component and is not permitted. A blowup has dense isomorphic open but fails monomorphism; a cusp normalization fails normal target. Thus neither is a false positive. The item itself was checked on Y=G and a fibrewise dense open Y of G, where the closed multiplication graph restricted to Y^3 gives exactly the stated projections and division domains.

No non-elementary step exceeds 2000 characters. Each step carries its argument instead of merely applying a new node for its conclusion. This checks B1--B10, C1--C8, D1--D5 and E1--E7 against the written files. No unfinished mathematical issue remains in the item's split; the new general lemma remains intentionally unsplit. No agents were started.

## Unfinished work

None for this one-level split. One new statement-only lemma is queued by the delivery; zero new Mathlib leaves.
