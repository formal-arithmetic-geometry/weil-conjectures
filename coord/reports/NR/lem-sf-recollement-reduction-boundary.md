# Stage-1 report: lem-sf-recollement-reduction-boundary

## Files written

- dag/nodes/sec-six-functors/lem-sf-recollement-reduction-boundary.json: statement, split; not a Mathlib leaf. Five proof steps reuse existing statements. No new nodes or Mathlib leaves.
- citations.json: ten entries, one for every step/node pair, each a verbatim substring of the cited statement.
- report.md: this report. searches.jsonl holds actual search results from msearch.py.

## Attachments

None. Searched the project library for the exact blueprint tag and for recollement, reduction, boundary and connecting maps. Read the declarations listed in ProEtale/Adic/Localization.lean and WeilSheaf/OpenClosedTriangle.lean. These concern closed-support recollement or compact-support images, not this specified coefficient-change isomorphism and its third square. No complete declaration of the item was found.

## WANTED

None. No source was downloaded or compiler invoked.

## Corrections and scope

The imported statement is retained exactly. Its source points to package clause (3), whose brief instruction to take the exact image of recollement does not spell out this coefficient boundary comparison. The split writes that argument; proof_origin is agent, not a claim that the blueprint provides the full argument. No STATEMENT-DISPUTED issue was found. The integral and finite ordinary derived categories remain distinct, related by the specified exact coefficient functor; this is not finite-to-finite reduction and needs no extra finite-Tor hypothesis.

The first two squares alone do not force the third square in arbitrary triangles. The essential input is the finite recollement theorem's stated boundary uniqueness from shifted open-to-closed orthogonality. The proof constructs the transported third arrow explicitly before invoking uniqueness, rather than asserting that a vertex comparison automatically preserves connecting arrows.

## Not duplicates

No new node is proposed, so there are no new/existing pairs. Searched the whole DAG for recollement and connecting/boundary reduction, and blueprint_refs.py for recollement, connecting and reduction. The existing all-stages recollement, operation reduction and derived change-of-rings nodes supply the ingredients; the parent strict-tower realization lemma uses this item and is not cited. Checked every dependency closure of the selected substantive inputs: none reaches this item.

## Review by NR

I read the chapter record sec-six-functors and unit sk-thm-sf-package, together with the current main-20261015 package proof, especially clause (3). The proof stays on its exact-image-of-localization route. I read the current blueprint operation-reduction proof in sec-six-functors-basics/sk-prop-sf-pf-reduction and the finite/integral portions of the all-stages recollement proof in sec-smooth-purity/sk-prop-sf-localization. I also read Stacks Tag 06YY, sites-cohomology-lemma-derived-base-change, directly in sites-cohomology.tex, with its tag verified in tags/tags, and BBD Proposition 1.1.9 and Corollaire 1.1.10(ii), printed pages 23-24 (PDF pages 24-25). No SGA source is used. There are no new-node sources to review.

For step 1 I opened def-weil-derived-complete-integral-detailed and lem-pur-derived-change-of-rings. The former explicitly requires every reduction to be bounded constructible; the latter explicitly gives an everywhere-defined exact coefficient-change functor of triangulated categories. Its identity-topos specialization uses the map from the completed ring sheaf to the constant quotient sheaf, precisely the map defining r_n. The shift comparison is part of this exact functor, not an omitted identification of graded objects.

For step 2 I opened lem-fix-operation-reduction. Its statement gives integral-to-finite comparisons for pullback, ordinary direct image and compact-support image on the stated bounded domains and explicitly says they preserve units and counits. The hypotheses here are exactly those domains. Thus the open counit and closed unit squares are actual identities for a_n and b_n. No internal-Hom perfectness or exceptional-adjoint claim is used.

For step 3 I read def-weil-pbc-triangles-with-shift and def-weil-triangulated-category. The first specifies all three squares and characterizes triangle isomorphisms by invertible components. Defining the transported arrow as a_n[1] d b_n^{-1} makes the third square an identity. The second supplies TR1, closure under triangle isomorphism. This is a short direct use of those definitions, correctly marked elementary; no independent cone-comparison lemma is hidden in it.

For step 4 I opened prop-sf-open-closed-triangle-all-stages, whose statement explicitly says the third arrow is uniquely determined by the first two. Its finite coefficient case applies to the given separated finite-type X and bounded constructible K_n; ell differs from the characteristic and n is positive. The Hom-vanishing direction is Hom(open[m], closed), as required by BBD's Hom^{-1}(first,third) criterion, not the reverse. Hence the transported distinguished completion and any chosen finite completion coincide. The displayed equality then follows by multiplication by b_n. This proves the substantive third square without introducing a lemma that restates it.

For step 5 the same all-stages statement explicitly supplies functoriality for integral and finite triangles; the comparison node and exact-functor structure supply the natural vertex and shift maps. The triangle-category definition says composition is componentwise, so vertexwise naturality proves naturality of the triangle isomorphism. I checked K=0, X empty, U empty, Z empty and n=1: zero vertices give unique zero boundary arrows; no cancellation by a nonzero object, nonempty support, or finite-Tor amplitude is used. Arbitrary choices of the two completing boundary maps are harmless because the cited theorem states uniqueness. All five steps are under 2000 characters and the full assembly is under 3000 characters.

The Mathlib searches were run through the required msearch command with two semantic phrasings, LeanSearch, Loogle and source grep. I read their returned hits. map_distinguished (Mathlib/CategoryTheory/Triangulated/Functor.lean:189-191) only maps an already given distinguished triangle under an already triangulated functor; it does not construct these ringed-site comparisons or their unit/counit compatibility. Spectral-object and generic derived-comparison hits also do not state the item. Existing inherited searches are retained, and appended search records are taken verbatim from the actual sandbox search log. No searches were invented.

The substantive citations from other units are declared in split_report.tool_uses: exact ringed-site coefficient change, operation/unit/counit comparisons, and recollement uniqueness/functoriality. They are generic tools for this coefficient compatibility argument, not replacements for a unit's geometric proof. Every use was checked against the node's statement itself and recorded in citations.json. No unresolved mathematical work remains in this one-level split.
