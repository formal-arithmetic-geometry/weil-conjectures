# Worker report: lem-weil-pbc-derived-adjunction-top-edge

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-derived-adjunction-top-edge.json: existing statement, now split in eight steps. The statement and statement dependencies are unchanged.
- citations.json: one verbatim statement quotation for every proof-step citation.
- report.md: this report. searches.jsonl was produced by the required search wrapper.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, canonical single-adjunction transpose, and top-cohomology notions. The existing top-homology base-change and unrelated Fourier/complex results do not state this adjunct/edge identity. The existing single-module transpose is only the normalization input, not this item. Read its project source and the pinned-adjunction shift source; no attachment of a partial result is claimed.

## WANTED

None. The proof is an agent assembly from documents already present, explicitly marked proof_origin.by = agent. It is not attributed verbatim to Tag 0BKJ.

## Corrections and route

The unsplit node supplied no proof. Its statement is sound and was retained, including the bound on C, the bounded-below hypothesis on K, the ordinary tensor pullback, and the fixed adjunction normalization. Its existing blueprint ancestry and exact from.place are preserved; same_as remains [] after whole-blueprint searches for adjunction/derived adjunct and cohomology-adjunction/edge descriptions. This is a generic compatibility below the coherent affine comparison input of the existing ancestry, not a change to the chapter or unit route.

The proof does not assume derived pullback is exact or that the single pullback comparison is an isomorphism in the derived category. Only its degree-q map is inverted. It does not assume the direct image of a K-injective is K-injective. Local sections of that image are interpreted through the cited local Leray comparison. It does not identify hypercohomology with global sections of a cohomology sheaf: the local-class edge is retained throughout.

A potential normalization ambiguity was made explicit in step 7. The comparison named p by the single-transpose node and the comparison c in the top-cohomology node agree because, on the identity of g* N, both have the same derived transpose, namely the ordinary unit followed by the single direct-image comparison. The hom-set bijection proves equality. This avoids tacitly substituting a differently normalized comparison.

## Mathlib and duplicate searches

Retained all inherited Mathlib records, then ran the wrapper for this item with LeanFinder, Loogle, grep, LeanSearch and a second LeanFinder phrasing. Read every returned hit and the general Adjunction.derived construction in Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean: its assumptions and conclusion construct an adjunction, not the local-class/top-cohomology identity. The second phrasing returned shift-compatible triangulated adjunctions and the standard t-structure, also only ingredients. The grep hits concern simplicial skeleton/truncation adjunctions. Loogle returned no hits. Exact query strings and actual returned names were appended from searches.jsonl. No query was invented and no unavailable service was recorded as absence.

Whole-DAG searches by title and statement located the existing orthogonality, both Hom exactness lemmas, full faithfulness of singles, the general truncation triangle and good truncations. They are cited directly; the short Hom factorization is written in the item's steps. No new node rephrases a clause of the item or an elementary argument.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs.

## Review by N0

I read coord/delivery-errors.md B through E in full, the worker and stage-1 rules, the three levels in SETUP.md, GOAL.md, and the chapter/unit records. For the mathematical source I read cohomology.tex Tag 0BKJ (lemma-sheafification-cohomology), including its actual kernel/image proof, and Tag 079W (lemma-adjoint). I read derived.tex Tag 08J5 (remark-truncation-distinguished-triangle), including the two successive truncation triangles, and Tag 05TC to check the upper-bound direction used by the existing top-pullback node. I read the statements of every node in citations.json, rather than using their proofs as an unstated interface. For the fixed normalization I also read CanonicalSingleAdjunctionTranspose.lean, CanonicalSingleDirectImageComparison.lean, and PinnedDerivedAdjunctionShifts.lean; no Lean was written or compiled.

Step 1 takes naturality in the derived object from lem-pc-ringed-space-sheafification-cohomology and lem-trf-unbounded-direct-image-section-presheaf. Both statements explicitly include that naturality, and the latter includes compatibility with opens. The module-sheafification definition supplies exactly the uniqueness that descends the displayed presheaf equality; the ordinary module adjunction node supplies the sectionwise scalar restriction. This proves naturality of this edge, rather than assuming an unspecified spectral-sequence edge.

Step 2 uses the actual map construction in lem-pc-canonical-single-direct-image-comparison and the arbitrary-K-injective-representative formula in def-pc-ringed-spaces-derived-direct-image. The positive-acyclicity hypothesis in the former is needed only for its separate isomorphism assertion, which is not used. Its statement also says the comparison map is constructed from the unit without that assertion. On every open, lambda identifies local derived sections and Theta takes a cocycle to its sheaf cohomology class. The section m is sent to r(m) and back to m under Hq(r); no lift of an arbitrary cohomology section is assumed. This is a direct normalization computation using the cited definitions, not a new comparison theorem. The shift sign does not change kernels, images, or this actual cocycle.

Step 3 uses the initial, arbitrary-abelian-category part of def-kun-truncations, not its later etale applications. Its good truncations retain the specified cohomology in the stated range and descend to D. The canonical triangle of lem-sf-derived-truncation-triangle applies to any integer b and any derived object, so it applies at q and q+1 here. The top-pullback node explicitly gives A <= q without a lower bound on C or flatness of g. Kernel/cokernel formulas identify tau >= q A with Hq(A)[-q] and tau <= q J with M[-q]. The identities on Hq of the projections and inclusion are specified, which is essential in steps 5 and 8.

Step 4 cites orthogonality with the two strictly separated pairs (q-1,q) and (q,q+1). The two cited Hom exactness statements have exactly the required variance and position: the source factorization uses Hom(-,J), and the target factorization uses Hom(Hq(A)[-q],-). The composites vanish by those bounds. Step 5 uses full faithfulness of the single embedding, shifted by the derived-category shift equivalence. Thus its module map is precisely Hq(h), since both truncation maps induce identity. These are two short explicit Hom factorizations and an application of full faithfulness, so they remain elementary steps with their non-elementary input statements cited. There is no separate hidden lemma to create.

Step 6 uses the *formula*, not merely existence, for kappa in lem-weil-pbc-derived-pullback-top-cohomology. The counit shift node supplies the same shift comparison. Consequently the candidate composite has exactly Hq(d), and the faithfulness just proved applies because its target is J >= q. Its source is A <= q; no claim of faithfulness for unrestricted objects is made. Ordinary adjunction defines b under precisely the item's hypotheses.

Step 7 uses the normalized single transpose, the pinned adjunction shifts, the pinned pullback counit shifts, and bifunctoriality from lem-pc-ringed-spaces-derived-adjoint. Each is an actual statement of the cited node. The identity specialization checks p = c before using the single-module formula. Naturality under tau_C and i gives the displayed derived equation, so no compatibility is hidden behind a word such as transport. These cross-unit facts are declared as generic tools in split_report.tool_uses with their individual purposes; none replaces a geometric step of the unit.

Step 8 uses only the already proved naturality twice and the cocycle normalization. Substituting the equation of step 7 cancels no edge isomorphism: Hq(i), Hq(j), and Hq(tau_C) are identity under the already specified canonical identifications. The resulting ordinary adjunct is b itself. Therefore this finishes the claimed identity for every d, not just a chosen representative.

I checked the zero objects, empty opens and empty schemes: all maps remain defined, the cocycle computation gives zero, and the Hom factorizations still apply. For g = id the normalized comparisons recover the cohomology map. Negative q is covered by integer shifts with the stated convention. If Hq(C) or Hq(K) vanishes, step 5 makes the corresponding map to J zero, exactly as required. Non-flat g is allowed because only kappa on top cohomology is invertible; a nonzero lower tail of C and higher tail of K cause no convergence assumption. The bounded-below K hypothesis is retained even though this argument uses no bound beyond the displayed truncations. All eight steps are below 2000 characters; none contains an omitted non-elementary comparison.

## Unfinished work

No mathematical work remains for this one-level split. The existing cited tools retain their own independent DAG work. Required remote dry run and delivery are performed after this report is written.
