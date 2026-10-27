# Stage-1 report: lem-per-postnikov-finite-cutoff-abutment

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-postnikov-finite-cutoff-abutment.json: statement, split; no Mathlib match for the full theorem. Five explicit proof steps, unchanged statement and statement dependencies.
- citations.json: verbatim statement excerpts for every step/node pair.
- report.md: this report. searches.jsonl records the command's actual outputs; write_split.py is sandbox-only preparation.

No new nodes; no new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, finite-cutoff/finiteCutoff spellings and Postnikov/half-plane/abutment notions. The project has TruncationHypercohomology, TruncationQuadrantVanishing, HalfPlaneConvergence and AbutmentImageFiltration declarations, but their functors come from left-exact functors between Grothendieck categories or their hypotheses already assume an invertible cocone. They do not state the present arbitrary homological-functor theorem with shifted amplitude, cutoff, image formula and naturality. This item has no attached Lean audit declaration. A sorry-free special case is not an attachment of the item.

## WANTED

None. All sources needed for this abstract argument are present.

## Corrections and scope

No statement dispute or source error was found. The item was a statement-only node created by the accepted re-split of lem-per-bounded-above-rhom-hyperext; its original statement, source, created record, blueprint provenance and four earlier Mathlib search records are retained. I added proof steps and the searches actually run for this dispatch. No Lean was written or compiled, no shared repository or launcher file was written, and no git command was run manually.

I read GOAL.md, the chapter and perverse unit records, SETUP.md's three levels, stages/1-dag.md, roles/worker.md, coord/brief-stage1.md and delivery-errors.md B–E. This is an abstract tool beneath the coefficient/duality chain of the ancestor's Step 1, not a replacement of the chapter or unit route. I read the current main-20261015 ancestor statement/proof and half-plane proof. The item already has precise blueprint.from.place and via; searches for half-plane, truncation, Postnikov and cutoff found no equivalent blueprint statement, so same_as remains empty. The unit's key statement is not this item; no unit fields were changed.

## Not duplicates

There are no new nodes and hence no new/existing pairs. Existing thm-sp-half-plane-convergence, lem-sf-derived-truncation-triangle, lem-sp-long-exact-of-triangle and lem-sp-couple-morphism are reused rather than restated as children. In particular I did not create a node for the elementary truncation-tail two-zero argument or for shifting the filtration index.

## Mathlib searches

The new dispatch searches are recorded verbatim by msearch in searches.jsonl and incorporated in the item's mathlib_searches. All four services answered successfully. I read the returned hits. The first LeanFinder phrasing found quasi-isomorphism criteria for truncation projections and DerivedCategory.isGE_iff/isLE_iff/zero-homology lemmas; the second found the three homologySequence_exact lemmas and fraction lemmas. These provide ingredients, not the conclusion for arbitrary T with shifted amplitude. Loogle with "SpectralSequence", "trunc" returned zero hits. The homology-directory grep returned zero; a second grep in the triangulated directory returned spectralObjectFunctor. I opened TStructure/SpectralObject.lean:130–159 and SpectralObject/HasSpectralSequence.lean:22–90: these construct truncation spectral objects/pages but do not assert the finite cutoff and natural actual-abutment filtration. LeanSearch returned truncLE/truncGE and shape embeddings. I also read HomologicalFunctor.lean:82–94, 218–239 and the existing long-exact node's precise Mathlib match. No recorded query was invented; no search service outage was recorded as absence.

## Review by NB

For the item I read Stacks homology.tex, Tag 011T (lemma-spectral-sequence-associated-exact-couple), including the canonical cycle/boundary and differential formulas, and derived.tex, Tag 08J5 (remark-truncation-distinguished-triangle) and Tag 0147 (definition-homological and the ensuing long exact sequence). Tag 011T alone does not assert this whole cutoff theorem: accordingly proof_origin.by is agent, and the proof explicitly combines those sources with the existing half-plane theorem. There are no new nodes needing additional source checks.

Step 1 uses the actual statements of def-sbc-standard-tstructure-derived-category (standard vanishing/truncation), def-weil-abstract-derived-category (cohomology, quasi-isomorphisms and localization) and def-sp-exact-couple (successive pages are cohomology). For q<c I verified cohomology is zero in every degree, so the map from zero is a quasi-isomorphism. For E support I applied the assumed amplitude bound to the specific heart object H^q(L)[-q], whose lower bound is q, rather than to L with an incorrect bound. This gives p<-r. Additivity preserves the zero objects. This is a short calculation from the stated definitions and hypotheses, marked elementary, not a new lemma.

Step 2 uses thm-sp-half-plane-convergence. I opened its full statement and checked both hypotheses separately using Step 1: D vanishes below c, and translated E vanishes unless P>=0 and Q>=c. The translation preserves all structure-map differences and exactness, including the boundary of degree (2,-1). I checked N=n+r and the canonical object at (0,N); it really is T^n(tau<=n+r L), not T^(n+r) of that object. The theorem supplies finite filtration, canonical stable-page/graded comparisons and stabilization at s>max(Q-c+1,P). The substitution P=p+r is written explicitly. Thus none of these conclusions is inferred from a mere definition node.

Step 3 cites lem-sf-derived-truncation-triangle and lem-sp-long-exact-of-triangle. I read both statements and their Mathlib interfaces: the former gives the canonical truncation triangle with K'=tau<=b-1 and K''=tau>=b, and the latter gives the long exact sequence for a general homological functor, not only derived direct images. With b=m+1, the amplitude assumption applies to the actual tail R_m in D>=m+1. I checked both strict inequalities n-1<m+1-r and n<m+1-r for every m>=n+r, including equality m=n+r. The resulting segment has zero on both ends; mono plus epi is the abelian-category isomorphism criterion. The naturality equation for a_n is displayed, so no completeness or infinite-limit argument is hidden. Canonical truncation naturality is from the standard truncation functors already named in the statement.

Step 4 uses thm-sp-half-plane-convergence's exact image formula and def-sp-filtration's subobject, quotient and finite/exhaustive/separated conventions. I checked N-P=n-p. For P>=0 the iterated alpha is the actual composite truncation inclusion; after a_n it is the inclusion into L. For P<=0, Step 3 independently gives the displayed image as the entire object, agreeing with the theorem. Quotient transport is explained by the commuting inclusions of the two adjacent images, not asserted without an argument. The upper endpoint is exactly n-p<c, or p>=n-c+1. When n+r<c the canonical object vanishes, so the actual abutment does too. These are elementary substitutions and the definition of quotient after the cited convergence theorem; no additional convergence theorem is hidden.

Step 5 uses lem-sp-couple-morphism, whose full statement explicitly gives filtered canonical abutment maps AND their compatibility with stable-page maps on associated graded pieces. I checked its hypotheses against the translated couples of Step 2. Its abutment map is the actual T^n(tau<=n+r u). The square from Step 3 identifies its conjugate with T^n(u), and the square at every cutoff k=n-p proves the image-subobject assertion. Uniqueness through the monic image inclusion identifies the restriction, and the cokernel universal property explains the quotient square. Thus this step does not take naturality of graded convergence from a node giving only page functoriality. It is a generic tool outside the perverse unit, declared in split_report.tool_uses; it does not change that unit's proof route.

I checked the small cases over vector spaces. For T^0=H^(-r), T^n(L)=H^(n-r)(L) would have the opposite amplitude convention; the correctly saturating test is T^0=H^r, giving T^n(L)=H^(n+r)(L). With L=k[-c], the unique nonzero abutment occurs at n=c-r and the unique nonzero graded spot is p=-r,q=c. The cutoff m=n+r=c includes that cohomology; a cutoff one smaller need not be an isomorphism, so the bound is sharp. For n<c-r both the diagonal support interval and abutment vanish. I also checked L=0, arbitrary positive and negative r, p=-r, p=n-c+1 and the empty interval: the endpoints and all shifts agree. No small-case correction to the statement was needed.

Against B–E: no new statement is incomplete or an extracted restatement, all cited node statements were read, every non-elementary input is explicitly cited, and quotations are verbatim from those statements. Every step is under 2000 characters; no long step hides a lemma. The tail isomorphism, index translation and transport are proved inline, rather than renamed into clause nodes. The report explains the agent/source boundary and the only off-unit tool use. No SGA source is used.

## Unfinished work

None at stage 1; server dry run and delivery results are recorded by the delivery command.
