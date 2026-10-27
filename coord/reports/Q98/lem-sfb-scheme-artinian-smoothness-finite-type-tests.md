# Q98 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-artinian-smoothness-finite-type-tests.json: split item; no exact Mathlib match. Four proof steps, eleven existing proof dependencies.
- citations.json: one verbatim statement quotation for each step/node citation.
- report.md and searches.jsonl: report and actual search log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched WeilConjectures for the blueprint tag and for Artinian smoothness/lifting. The project theorem AlgebraicGeometry.smooth_near_iff_artinian_lifting_at_point (SmoothArtinianLiftingAtPoint.lean:200) tests all small extensions at a point; it does not assert the global criterion with finite-type bottom maps. Its statement therefore does not attach this item, regardless of the status of its dependencies. The existing fixed-residue node is precisely the variant needed here.

## WANTED

None. All sources needed are present locally.

## Corrections and scope

The imported item is correct: no statement change or STATEMENT-DISPUTED. Its proof was absent. The square-zero condition really is redundant, as the elementary simple-module argument in step 3 shows. I preserved every inherited metadata and search field, and appended only the actual Q98 logged searches. No Lean was written, no compiler was run, and no project or launcher file was changed.

The existing Artinian finite-type residue node states an affine algebra assertion, not the whole scheme-valued Tag 02HV. Step 2 explicitly handles each affine open of V, applies that algebra assertion there, and checks quasi-compactness using the one-point source. Step 1 proves the necessary composition of finite generation with explicit generators, so it does not misuse the finite-type composition node with the merely locally finite-type morphism f.

## Not duplicates

No new nodes. Reused the existing fixed-residue smoothness test, Artinian finite-type residue criterion, and finite type points detecting opens. Whole-DAG tag and keyword searches and whole imported-blueprint searches (artinian, smoothness, small extension, 02HY) found no additional exact statement to replace this item. The ancestor command returns None; the existing null ancestor and via chain are preserved. I read the current latest direct-images proof and the unit record; this is the inherited local deformation prerequisite, without a change to its route.

## Review by Q98

I read Stacks more-morphisms.tex, Tag 02HY (lemma-lifting-along-artinian), including its contradiction argument, and Tag 02HX (lemma-lifting-along-artinian-at-point), especially condition (4). I also read morphisms.tex Tag 02HV (lemma-artinian-finite-type), and algebra.tex Tag 02HS (definition-small-extension) and its following observation. There are no new-node sources to review. I checked each of the eleven existing cited node statements directly, and citations.json copies their statements verbatim rather than quoting their proofs.

Step 1 uses the affine-opens basis to choose U inside f inverse D and the factor-through-open statement to put the canonical residue point in U. The affine-pairs finite-type statement supplies both finite generations, one from f and one from the finite type point map; the finite type point node supplies the exact meaning of the latter. The images of the two finite generating sets generate k over R, so no unproved permanence assertion is concealed here.

Step 2 uses exactly the Artinian unique-prime assertion to identify the image of c with f(w), the factor-through-open assertion for each D, and the affine spectrum correspondence to read its ring map and residue composite. The existing Artinian finite-type node applies with its ring R and its Artinian local ring B prime, without a Noetherian hypothesis on R. It supplies finite generation from the residue field, which step 1 supplied for every affine D. The finite-type definition then gives local finite type and quasi-compactness: all preimages of affine opens are empty or one-point spaces. This checks the finite-type hypothesis of the item, not just local finite type.

Step 3 uses the module-length definition only for the short derivation that I is simple and square zero. The quotient B is nonzero since it is local with residue field k; hence I is proper and lies in the maximal ideal. The fixed-residue criterion's local finite-type and locally Noetherian hypotheses are exactly those of the item, and step 2 proves its arbitrary fixed-residue bottom maps finite type. The assumed lifting then gives every diagram required by that criterion, which concludes a smooth open neighbourhood. No assumption about separability of k, global separation, or quasi-compactness was introduced.

Step 4 uses the finite type point lemma's exact consequence about opens, not density of closed points on a Jacobson scheme. Every finite type point lies in a smooth open by step 3, so the union is the whole scheme. The source-local smoothness statement then applies to that open covering. Its empty-family clause handles W empty.

I tested the statement against an empty source, a field-valued source, non-Jacobson bases (so globally closed points would be insufficient), non-quasi-compact sources and non-separated sources. The proof only chooses affine neighbourhoods individually and never intersects two affine opens claiming the intersection affine. For the convention on small extensions, a length-one kernel is nonzero and simple; the zero kernel is not erroneously included. The four steps have lengths below 1000 characters each and hide no long-step lemma. The Mathlib searches in the actual log returned the definition/local chart characterization of smoothness and forward lifting for formally smooth algebras, not this reverse Artinian criterion. All recorded query strings match commands actually run; the inherited records are left intact.

## Unfinished work

None within the stage-1 split. Existing unsplit dependencies remain their own future items. Mechanical dry run and delivery follow this report.
