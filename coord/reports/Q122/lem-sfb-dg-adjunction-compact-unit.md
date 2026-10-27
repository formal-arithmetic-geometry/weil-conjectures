# Q122: lem-sfb-dg-adjunction-compact-unit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dg-adjunction-compact-unit.json: item, split into five steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-dg-property-p-devissage.json: statement-only, unsplit, no Mathlib match. It states the closure criterion of Stacks Tag 0FQE for an arbitrary dg algebra.
- citations.json: verbatim statement extracts for all nine step citations.
- searches.jsonl: actual msearch.py log; queries reused only after reading their returned results.

## Attachments

None. The project-source searches by blueprint tag, dg modules, regular modules, compactness and adjunction units found no declaration stating this item. DerivedModuleFreeGeneration.lean handles ordinary modules over an ordinary commutative ring, not arbitrary dg algebras. Existing ShiftSaturatedIsoLocus and CompactTestsRightAdjointCoproducts declarations supply generic intermediate facts, not this item.

## WANTED

None for this split. The proof and new node follow the local Stacks corpus. The existing generic dg-projective-resolution node records its own broader literature provenance; this delivery creates no new assertion about higher coherence.

## Corrections and scope

The item statement is correct and was preserved. Its source is a relative abstraction of Tag 09LZ, not that tag's literal ringed-site tensor statement. The abstract proof only needs compactness of T(A) in the actual target, so it does not assume generation of that target or compactness in a larger ambient category. Tag 09LZ's sentence saying its tensor functor 'has a left adjoint' reverses the adjunction named immediately afterwards; its displayed adjunction and intended argument use RHom as right adjoint. The item and split use the specified T left adjoint to R throughout.

The initial draft separated derived Hom from A[n] into a node. On reading the full statements of the existing general dg-projective nodes, I removed that draft node: the one-generator semi-free case and evaluation at 1 give this calculation in a few lines. Only the genuine property-(P) devissage theorem remains new.

No Lean files or compilers were used; all writes are in this sandbox. The current blueprint is literature/blueprint/latest, whose sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3) supplies the inherited direct-image supporting path. The inherited blueprint.from.node is null because the existing ancestor chain is broken; the explicit place and via chain were retained, and the new node prepends this item as required by blueprint_refs.py ancestor (which printed None).

## Not duplicates

lem-sfb-dg-property-p-devissage vs lem-pc-derived-module-free-generation: the latter concerns the ordinary derived category of modules over an ordinary ring; the new node concerns right modules over an arbitrary unbounded differential graded algebra and the property closure criterion of 0FQE, not 09PB.
lem-sfb-dg-property-p-devissage vs lem-sfb-dg-countable-semi-free-resolution: that node requires a countable dg algebra and countable cohomology and constructs a countable resolution; the new node imposes no countability assumptions and concludes a closure property on every derived object.
lem-sfb-dg-property-p-devissage vs lem-coef-dg-module-semi-free-replacement: that node constructs a semi-free resolution; it does not state the propagation of an arbitrary property through derived distinguished triangles and coproducts.
lem-sfb-dg-property-p-devissage vs lem-sfb-dg-sequential-colimit-triangle: that node identifies a specified dg-module sequential colimit with its telescope triangle and states the coproduct formula, rather than generation by regular-module shifts.
lem-sfb-dg-property-p-devissage vs lem-sfb-dg-adjunction-compact-unit: the new statement has no adjunction, functors, compactness or unit; it is the general dg closure input, not a clause or relabelling of the item.

No existing source field has Stacks Tag 0FQE. I searched all node statements/titles/source fields for dg generation, regular modules, property (P), semi-free modules and compact adjoint tests, then read the candidate statements. Blueprint searches for differential graded, property (P), regular module, P-resolution, compact generator, 0FQE, 09K1 and 09KY gave no matching blueprint statement. The unrelated regular-module and constructible-generator hits were read as search results, not treated as matches. Project-source searches likewise found no general dg-generation declaration.

## Review by Q122

I read Stacks dga.tex Tag 09LZ, lemma-fully-faithful-in-compact-case, including its reduction from property-(P) resolutions to regular-module shifts, and Tag 0FQE, remark-P-resolution, including its three explicit closure hypotheses and its cited property-(P) sequence/resolution inputs. For the new devissage node, I also read Tag 09KL's sequence and Tag 09KP's resolution statement. The new statement restates the general closure criterion, spells out its dg algebra/module/derived-category meanings, and adds no countability restriction. Its proof and proof dependencies are empty because it is a new unsplit input. I read 09K1 and 09KY while assessing the Hom comparison; rather than duplicate it, I used the already available general projective-module statement.

Step 1 uses the exact coproduct clause of lem-sfb-dg-sequential-colimit-triangle, not its telescope proof. It applies lem-coef-dg-semi-free-homotopically-projective to the one-object dg category with endomorphisms A: the single shifted representable has a one-stage filtration, so every hypothesis of semi-freeness holds. The mapping-complex clause of lem-coef-dg-module-projective-resolution then applies. A degree-r graded map is determined by the image of the closed generator 1 in degree r-n, and its Hom-complex differential evaluates to d_M of that image. This proves the degree-zero cohomology comparison without using an unrecorded derived-Yoneda theorem. Cycles and boundaries of sums have finite support, proving sum compatibility directly. The compactness definition cited is exactly the canonical direct-sum-of-Hom criterion. Applying inverse shifts to a coproduct proves compactness for shifts of T(A); no extra generator hypothesis is used.

Step 2 applies the new devissage statement to the object property of belonging to the full replete localizing closure of all A[n]. Empty sums give zero and the definition of a triangulated subcategory gives two-out-of-three. Thus every object belongs to this closure. I opened lem-sf-localizing-hom-test: it explicitly assumes both ends of a morphism lie in that closure and gives isomorphism detection by every shifted generator. Here both ends do lie there, and the set of all A[n] already contains all its shifts. This verifies its actual hypotheses, rather than citing a definition as a generation theorem.

Step 3 uses precisely the conclusion of lem-sc-compact-tests-right-adjoint-coproducts. The indexing family is Z in the common universe, all its source and left-adjoint images are compact by step 1, and it detects isomorphisms by step 2. The target is locally small in the Hom/indexing universe used for the statement, and both sides have the required small coproducts. The explicit Hom calculation on coprojections identifies the canonical comparison; it does not merely assert an abstract isomorphism between its endpoints. This works when the coproduct is empty as well.

Step 4 uses the full closure sentence in lem-sc-shift-saturated-iso-locus, read from its statement. Both functors id and RT are exact and preserve coproducts, the latter by step 3 and the hypothesis on T. The locus is shift-saturated, so that generic node applies even without relying on a bare natural transformation to commute with boundaries. Here the specified adjunction is shift-compatible as additionally assumed: conjugating eta_A by its structural shift isomorphisms proves invertibility at all A[k]. The new devissage node is then applied to a property having all three stated closure conditions. Its n=0 conclusion is exactly invertibility of eta_M, with no change to the unit.

Step 5 is elementary adjunction algebra: under the actual adjunction bijection, T(f) corresponds to eta_N composed with f. Postcomposition with eta_N inverse cancels it, proving the Hom-set bijection. It needs no new node for the generic Mathlib fullyFaithfulLOfIsIsoUnit theorem. I nevertheless searched and read that declaration at Mathlib/CategoryTheory/Adjunction/FullyFaithful.lean:143: it assumes all components of the unit are already invertible, so it proves the final assembly but does not prove the item.

Mathlib searches were executed only through msearch.py. LeanFinder/LeanSearch returned ordinary cochain-complex, Ext, projective-resolution, triangulated-object-property and ordinary DerivedCategory declarations. I read HomComplexCohomology.lean's scope and the full faithfulness source; neither supplies dg-algebra generation. Two semantic phrasings of the new devissage statement returned no matching result. The successful Loogle searches for IsCompactObject/DerivedCategory and DGModule, and targeted source greps, found no dg-generation theorem. One earlier Loogle string was a syntax-error query and is not used as absence evidence or recorded in the node. There are no Mathlib leaves in this delivery.

I checked B1-B10: the one new node is self-contained, statement-only, with inline notions or exact definition citations, single TeX escaping, correct source label/tag and blueprint attribution, real logged searches, and no attachment or duplicate. I checked C1-C8: each non-elementary input is a cited statement, the citation quotes are verbatim, and the five generic off-unit tools are declared in split_report.tool_uses. I checked D1-D5: the item carries the adjunction, comparison, compactness and unit propagation argument; the child contains only the independent generation criterion. I checked E1-E7: arbitrary nonconnective and noncommutative dg algebras, zero algebra/zero modules, empty coproducts, unrestricted module size within the fixed universe, and targets with an extra summand orthogonal to T(A) do not invalidate the proof. In particular the extra-target-summand example confirms that no detection by T(A) in the target was assumed. Every proof step is under 2000 characters.

## Unfinished work

The new property-(P) devissage node is intentionally unsplit, as required for a one-level stage-1 split. No requested part of the item's proof remains unwritten. Independent maintainer review follows delivery.
