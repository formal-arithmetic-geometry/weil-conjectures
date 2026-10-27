# Q152: lem-sfb-permissible-dilatation-section-estimate

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-permissible-dilatation-section-estimate.json`: item, split; statement unchanged, seven proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-adapted-smooth-ambient.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-centre-dilatation-coordinates.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-relation-minors-length.json`: statement, unsplit; no Mathlib match.
- `citations.json`: one exact statement quotation for each of the twelve citations in the item.

## Attachments

None. Searched `lean/WeilConjectures` for the item tag, dilatation, smoothness defect, cotangent presentations and prospective new ids. No project declaration states the item or any new lemma. General existing cotangent declarations do not supply the adapted ambient or dilatation assertions.

## Wanted literature

WANTED: Bosch–Lütkebohmert–Raynaud, *Néron Models*, 3.2 Proposition 3, 3.3 Lemma 2 and Proposition 5, printed pp.64, 66, 68–71, for this item and all three new nodes. The named local PDF is absent. I read the primary-source scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf (PDF pages 70, 72, 74–77); the split is conservatively marked agent-origin because the document is not available under literature/. No literature, repository or launcher file was changed.

## Findings and route

The statement is precisely the local version of BLR 3.3 Proposition 5. No hypothesis or conclusion was changed. BLR works with finite type; its proof begins by localizing around the closed image of the chosen section, so locally finite type suffices. The proof needs neither a group law nor a uniform bound over sections, and makes no quasi-compactness inference for the original X or Y.

The source's central argument is retained in the item: using the ambient cotangent isomorphism, an equation f in H is pi*g plus a term in J squared, and condition (N) forces g into J. The item then forms f/pi squared, calculates its differential coefficients, and compares the selected minors. None of the three new nodes states defect decrease, condition (N), or a clause of the final inequality. They are independent tools, respectively local embedding geometry, an affine etale-coordinate base change, and finite-module linear algebra.

The zero-rank case is proved directly rather than invoking BLR's ambient-dimension argument: after passing to Frac(A), the two relation modules have the same rank; rank zero submodules of A^N vanish. This avoids importing dimension constancy or an unproved smoothness criterion. I removed an unnecessary assertion about flatness of the dilatation quotient during self-review, since its proof would call for an additional theorem and it is not used.

Read the latest chapter and unit at `literature/blueprint/latest/blueprint/sec-six-functors-basics/`, including `sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. The DAG unit record still has its historical different chapter/path; neither chapter nor unit was edited. `blueprint_refs.py ancestor` explicitly reports from.node=None for this inherited chain; that null is retained, with precise BLR proof places and the full inherited via list. This supplies the existing trait/Neron prerequisite below direct-image finiteness, without replacing an alteration or six-functor route.

Tool uses of the off-unit DVR and maximal-ideal lemmas are declared in split_report. They supply only the basic strict-henselization properties. The differential quotient and localization lemmas are existing Mathlib leaves.

## Searches

Before creating nodes I searched the entire DAG for dilatation, conormal sequences, adapted/minimal smooth ambient embeddings, cotangent restrictions, torsion/minors, elementary divisors and Smith form. Blueprint searches for dilatation, Jacobian, differentials, minor, ambient, cotangent and smooth centre found no matching blueprint assertion. The promising DAG statements are compared below. Existing conormal exactness, localization, DVR preservation and maximal-ideal extension are reused.

All new-node searches ran through the required msearch.py and their actual query/result records are preserved in searches.jsonl. Each new node has LeanSearch, Loogle, grep, and two LeanFinder phrasings. All services returned successfully. Smoothness hits such as IsSmooth.exists_isStandardSmooth and SubmersivePresentation.basisKaehler start from a smooth algebra/presentation; they do not construct the smooth ambient embedding from a nonsmooth X, or the dilatation algebra. I inspected Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean, especially basisKaehler at line 226, and Extension/Cotangent/Basic.lean at line 60. For the minors lemma I inspected Submodule.finrank_quotient_eq_sum in LinearAlgebra/FreeModule/Finite/Quotient.lean at line 126: it concerns field dimensions with extra scalar and freeness assumptions, not arbitrary DVR torsion length or maximal-rank minors. It therefore does not give a one-line specialization. No Mathlib leaf is claimed.

## Not duplicates

lem-sfb-adapted-smooth-ambient vs lem-trf-minimal-envelope-coefficient-comparison: the latter is over Q for reduced schemes and includes resolution-invariant comparison; it does not construct an ambient scheme over a DVR adapted along an entire smooth special-fibre subscheme.

lem-sfb-adapted-smooth-ambient vs lem-trf-cotangent-isomorphism-coordinate-lift: the latter assumes both smooth ambient embeddings over a field are already given; the new statement constructs one over a DVR and fixes the centre ideal.

lem-sfb-adapted-smooth-ambient vs lem-pur-smooth-pair-local-coordinates: the latter assumes X and Y smooth over the same base. Here X need not be smooth and Y is smooth only over the residue field.

lem-sfb-adapted-smooth-ambient vs lem-pur-smooth-closed-coordinate-lift: the latter assumes a regular sequence cutting out Y and only gives a map to affine space; it supplies no closed embedding into a smooth envelope with the required cotangent restriction isomorphism.

lem-sfb-smooth-centre-dilatation-coordinates vs lem-sfb-group-dilatation-universal-property: the latter concerns group schemes and the group law/universal property, not the etale coordinate ring, smoothness and differential basis of an ambient chart.

lem-sfb-smooth-centre-dilatation-coordinates vs lem-sfb-binomial-blowup-chart-algebras: the latter only treats R[x,y]/(xy-a^n), not arbitrary etale coordinate algebras or their differential bases.

lem-sfb-dvr-relation-minors-length vs lem-sc-dvr-saturation-line-smith-normal-form: the existing Mathlib leaf gives diagonal bases; it does not state torsion length, normalized valuations or their equality with the determinantal divisor. It will be a useful dependency when the new lemma is split.

lem-sfb-adapted-smooth-ambient vs lem-sfb-permissible-dilatation-section-estimate: both refer to BLR 3.3 Proposition 5, but the new lemma concerns ambient coordinates and assumes no section density; it states no inequality.

lem-sfb-smooth-centre-dilatation-coordinates vs lem-sfb-permissible-dilatation-section-estimate: the new node treats only an ambient etale algebra, with no nonsmooth quotient, (N) or defect.

lem-sfb-dvr-relation-minors-length vs lem-sfb-trait-section-differential-defect-criterion: the latter identifies the zero of a section's defect with smoothness; it states no matrix-minor formula.

## Review by Q152

I read BLR 3.3 Proposition 5 and its proof on printed pp.68–71 for the item, its adapted-coordinate construction on pp.68–69 for the ambient lemma, 3.2 Proposition 3 with the p.70 chart construction for the coordinate dilatation lemma, and the relation-module calculation in 3.3 Lemma 2 on p.66 for the matrix lemma. I also opened Stacks algebra.tex Tag 00RU, lemma-differential-seq, and more-algebra.tex Tag 0AP3, lemma-henselization-dvr, rather than inferring their claims from titles. All nodes cited by the item were opened and their complete statements are quoted verbatim in citations.json.

Step 1 takes exactly DVR preservation from lem-sc-strict-henselization-dvr and extension of the maximal ideal from lem-sc-ring-strict-henselization-local-maximal-ideal, so pi is still a uniformizer. Its use of the ambient lemma checks local finite type, smoothness of U and freeness of the differential restriction, precisely the hypotheses given. It takes the differential localization isomorphism from the localization leaf. Restricting to an open containing the closed image loses no part of a section, and (N) applies to the resulting affine W.

Step 2 uses the ambient node's isomorphism on W and its displayed differential basis. It proves H contained in J squared in the item: differentiation kills f on X, independence kills the normal coefficients modulo J, and cancellation of pi in A plus (N) kills the remaining coefficient. In particular this is schematic vanishing, not just containment of topological images.

Step 3 checks that the ambient node supplies an etale coordinate morphism, the actual hypothesis of the chart lemma. Its statements give C' and the differential basis. The saturation argument is written explicitly as the kernel of C' to D[1/pi]. Every map to A kills that kernel because A has no pi-torsion, and the fractions determine the lift uniquely. No general group-dilatation theorem is used for a nongroup X.

Step 4 uses exactly the flatness and differential transformation in the coordinate lemma to cancel pi and pi squared. The row formula divides y columns by pi squared and normal columns by pi, not both by the same factor. This is the calculation needed for the improvement.

Step 5 uses the two coordinate nodes' Noetherian clauses to choose finite equation lists, and the exact cokernel assertion of the existing 00RU leaf for each quotient. The preservation of this presentation after tensoring is justified by its quotient universal property; injectivity on the left is neither asserted nor needed. Step 6 uses only the coordinate lemma's equality after inverting pi and explicitly verifies the ideal saturation and evaluation of differentials kill the coefficient-derivative terms. Thus the two relation ranks really agree, without an assumed fibre dimension identity.

Step 7 uses the matrix lemma twice with these finite presentations and equal ranks. Adding the rows of the divided equations leaves L' unchanged. A selected minor with p tangential columns acquires valuation decrease q+p, which is at least one when q>0. At q=0 both modules are free, so the maximum formula also holds when delta=0. The finite-length assertion in the matrix lemma also ensures that the defects used here are honest finite integers.

Small cases checked: H=0 (smooth ambient X), n=0, r=0, empty matrix and N=0, q=0, positive rank with zero minors, and a single row [pi^e] (torsion length e). For X=Spec R[x,y]/(xy-pi^2) and centre (pi,x,y), the section x=y=pi has delta=1 and the divided equation x'y'-1 gives delta'=0, agreeing with the inequality. With an empty U there is no section to consider. The new ambient lemma does not need (N); the chart lemma is a polynomial etale base change, even in mixed characteristic; the minors lemma does not assume a coefficient field. The item never assumes R excellent or X quasi-compact.

All new nodes contain statements only and have distinct mathematical roles. Each non-elementary step cites the nodes that state its inputs; the elementary steps are the displayed coefficient, saturation and localization calculations. No proof step exceeds 2000 characters. No false statement or statement dispute was found; the item was not weakened. No SGA route was used.

## Unfinished work

No part of the item's assembly proof is deferred. The three new statements are deliberately unsplit stage-1 inputs. Server verification and delivery results are recorded below after running the prescribed tool.

## Verification

The required `deliver.py Q152 lem-sfb-permissible-dilatation-section-estimate --no-push` exited 0 and printed `OK (not pushed)` at b49f3588812 with server preflight passed. No diagnostics required repair. This ran the prescribed server checks; no local DAG checker, Lean compiler, Lake or build command was invoked.
