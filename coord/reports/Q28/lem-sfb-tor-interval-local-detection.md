# Q28: lem-sfb-tor-interval-local-detection

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-tor-interval-local-detection.json`: statement, split into four proof steps; not a Mathlib leaf. No new nodes.
- `citations.json`: nine verbatim statement excerpts, one for every cited node in every step.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `write_split.py` is sandbox-only preparation.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and the Tor-amplitude/detection notions. The exact tag is absent. `AlgebraicGeometry.ProEtale.torAmplitudeIn_of_mapDerivedCategory_upperStar` in `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/LocalizationFiniteTor.lean:190` proves an open-closed assertion for constant coefficient modules and assumes a Noetherian coefficient ring. It does not state clause (i), and its coefficient category is not arbitrary sheaves of rings. It is therefore partial coverage and cannot attach this item. The scheme structure-sheaf open-neighbourhood results are likewise different statements.

## WANTED

None. All documents actually used are present.

## Audit findings and changes

The statement is unchanged. The item was an unsplit statement created for `det-def-localizing-closure-ctf-equals-bc`; no previous sandbox split or report existed. I retained the repository's statement, provenance, blueprint fields and historical Mathlib searches, and appended this group's actual logged searches. The proof is marked agent-written because it assembles the existing general tools into the blueprint's restriction argument rather than claiming that Stacks states this exact two-clause theorem.

I read the current main-20261015 chapter, localizing-closure unit and ancestor proof. The unit has no numbered proof steps to populate, and this item is not its key definition. The ancestor's Locality uses exact, tensor-compatible, conservative restriction; Strata uses an open-closed localization sequence and tensor. This item's intended restriction/detection variant is precisely implemented: step 3 proves cover locality and step 4 detects cohomology through the open and closed restrictions. No projection formula, constructibility assumption or finite-stratification assertion is used.

I did not use `lem-zl-condensed-cover-restriction-conservative`, whose statement requires a pulled-back condensed coefficient ring, or `prop-weil-pbc-inverse-image-exact`, whose statement is etale rather than pro-etale. The arbitrary-geometric-morphism exactness tool and the category-valued sheaf cover-local theorem have the required scope. Likewise I use the abelian-sheaf clause, not the constant-module clause, of the site-object restriction theorem. These choices avoid importing unsupported coefficient assumptions.

## Mathlib and duplicate searches

Ran leanfinder, loogle, grep and leansearch through the required `msearch.py` command, and then a second leanfinder formulation and a focused grep in `Algebra/Homology`. The exact query strings and actual returned hit names are appended to the item and are in `searches.jsonl`. Every service answered. Hits for derived-category degree bounds, projectively defined Tor, exact functors and ordinary sheaf infrastructure do not state this arbitrary-ring-sheaf Tor-locality theorem. The 21 broad grep hits are unrelated ultrametric closed-ball results; the focused Tor-amplitude grep has zero hits.

Searched the DAG and whole blueprint for Tor amplitude, Tor bounds, detection, conservative restrictions, geometric inverse-image exactness and the relevant existing tools. Opened every cited statement. Existing `lem-sfb-sheaf-cover-local-isomorphism` is already a Mathlib leaf, `CategoryTheory.Sheaf.isIso_of_coversTop`; I read `Mathlib/CategoryTheory/Sites/LocalProperties.lean:35-64` and cited that node rather than creating a new leaf.

## Not duplicates

No new nodes. The existing tools are reused without restating them as auxiliary nodes.

## Review by Q28

I checked delivery-errors B to E against the actual statements and the local literature. For the item, I read the current ancestor proof's Locality and Strata paragraphs. For exact inverse image I read Stacks Tag 04JC, `sites-modules.tex`, `lemma-flat-pullback-exact`, including its distinction between abelian inverse image and extension of scalars. For derived tensor I read Tag 07A4, `sites-cohomology.tex`, `lemma-pullback-tensor-product`, and Tag 0G7E, `lemma-pullback-K-flat`. For restriction and covers I read Tag 03CE, `sites.tex`, `lemma-localize-given-products`, and Tag 04TQ, `lemma-glue-maps`, together with the existing Mathlib leaf. For open-closed detection I read Tag 09AH, `proetale.tex`, `lemma-ses-associated-to-open`, whose hypothesis is that the complementary open immersion is a quasi-compact morphism. For exact derived functors/cohomology I read Tag 015F, `derived.tex`, `lemma-right-derived-exact-functor`, and Tag 010N, `homology.tex`, `lemma-exact-functor`. There are no new-node sources to review.

Step 1 uses `lem-trf-geometric-inverse-image-exact` exactly for transported module inverse image over the inverse-image ring. `lem-weil-pbc-exact-functor-derived-factorization` states that the induced functor is represented termwise on every complex; `lem-weil-pbc-exact-functor-derived-functor` identifies it with the left derived functor as well as the right derived one. `lem-weil-pbc-exact-functor-complex-cohomology` explicitly gives the natural cohomology comparison for exact functors. These statements justify all of the step, including unbounded complexes and modules in degree zero. Small sites are the chosen skeletons in the statement's existing site/inverse-image conventions.

Step 2 cites `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Its statement includes arbitrary commutative ring sheaves, unbounded derived categories and the displayed tensor comparison. I checked the structural ring map is the identity from `f^{-1}A` to itself, so its module pullback agrees with the exact inverse image in step 1. In particular no flatness of `A`, no coefficient constancy and no extra boundedness is asserted.

Step 3 fixes an arbitrary global test module M; its inverse images are legitimate local test modules, so the same given endpoints apply to every i. `lem-sfb-proetale-object-inverse-image-restriction` explicitly covers all underlying abelian sheaves, and is used only in that generality; its separate constant-ring parameter can be Z. `def-weil-pbc-proetale-site` supplies the site and covering-family convention. Pulling the given cover back to each W supplies precisely the covering-sieve hypothesis of `lem-sfb-sheaf-cover-local-isomorphism`, whose statement is an isomorphism criterion for arbitrary category-valued sheaves. Applying it in abelian groups to F -> 0 proves the desired module sheaf is zero, since its underlying sheaf is zero. Thus no claim about arbitrary ring-sheaf coefficients is borrowed from a constant-coefficient module clause.

Step 4 uses `lem-exc-open-closed-detection`, whose statement explicitly allows an arbitrary commutative ring sheaf and exactly the stated quasi-compact-open-complement hypotheses. I checked it is the module sheaf H^q(K tensor^L M), not K itself or its original cohomology, to which that lemma is applied. The two vanishings are obtained by steps 1 and 2 and by the local Tor hypotheses, so the citation takes only the zero-detection conclusion its statement actually gives. Identity coefficient identifications instantiate its ring conventions.

I tested the empty scheme (including the empty covering), the zero ring sheaf, K=0, c=d, a cover consisting of the identity, Z empty or U empty, and a complex whose cohomology lies outside the proposed interval. The argument either gives vacuous zero sheaves or uses exactly the nonzero test that would fail locally; it never enlarges the interval or assumes a finite cover. In particular quasi-compactness is retained as a property of j, not replaced by quasi-compactness of X or U. No quasi-coherence or Noetherian hypothesis enters any tool. All nine quoted excerpts were asserted to be literal substrings of the cited node's statement before writing `citations.json`. I checked the citation graph has no path from any used node back to this item. Each step is under 2000 characters; the general comparison and detection lemmas already have nodes, so no hidden lemma needs a new one.

The off-unit statements are generic tools and are explained individually in `split_report.tool_uses`; they implement the unit's Locality/Strata route. The same list also documents the already-Mathlib cohomology and cover-local tools. No chapter/unit route or target statement was changed, no new lemma merely restates either clause, and no Lean was written or compiled.

## Unfinished work

None in the authorized one-level split. Existing cited nodes retain their own independent proof status.
