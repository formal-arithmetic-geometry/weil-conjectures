# Stage-1 delivery: lem-sfb-lattice-evaluation-derived-counit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-lattice-evaluation-derived-counit.json: existing statement, now split into seven proof steps, using thirteen existing nodes. Statement and statement dependencies retained. No new nodes and no new Mathlib leaves.
- citations.json: verbatim statements for every citation in every proof step.
- searches.jsonl: actual msearch.py query records, retained unchanged.

## Attachments

None. Searched lean/WeilConjectures by the exact item id, cubical evaluation, lattice counit, Koszul and invariants. Ordinary representation results and general derived-adjunction declarations do not state the full internal cubical evaluation formula and tensor normalization.

## WANTED

WANTED: an external published reference stating the specific signed internal cubical evaluation roof and its equality with the computation-unit-normalized derived invariant counit. The blueprint gives only the geometric route; the supplied proof is explicitly agent-written. Its categorical ingredients are sourced below.

## Corrections and scope

The item previously had no proof. Its statement needs no correction. No STATEMENT-DISPUTED claim is made. The proof avoids assuming an arbitrary ordinary tensor of quasi-isomorphisms is a quasi-isomorphism: tensor compatibility is explicitly in the derived categories. Ordinary augmentation denominators are invertible by the existing cubical statement, including on nonflat input.

The nearest-blueprint-ancestor command returns None for this existing created-node chain. I retained the recorded null ancestor and via list rather than inventing an ancestor, retained the precise from.place, and recorded paragraph (3) in split_report.blueprint. Whole-blueprint searches for cubical and injective counit returned no matches. Searches for counit, derived adjunction, and flat resolutions identified only reusable general tools, which are cited. The item is not the key node of its unit, so no unit record is changed.

Five existing off-unit statements are generic tools: internal/section tensor equivalence; closed tensor of module sheaves on a ringed site; independent-universe functorial flat resolutions; bounded-below derived-adjunction counit factorization; and generic derived strong tensor normalization. Each is declared, with its purpose, in split_report.tool_uses for maintainer review. No geometric route is replaced.

## Not duplicates

No new node was created. Existing generic ringed-site, derived-adjunction and tensor statements were reused instead of making specialized restatements of the item's clauses.

## Review by Q04

I read the current main-20261015 direct-images proof, paragraph (3), and the stored chapter and unit records. Paragraph (3) establishes the ordinary-open-direct-image route but does not provide this structural lattice computation; accordingly proof_origin is agent, not document. I read the statements of every cited node in full and checked the following uses against them.

Step 1 uses the condensed-action injective infrastructure for exactly its two Grothendieck structures, exact conservative forgetting and invariant-normalized adjunction. The internal/section tensor comparison supplies its pure-tensor and signed-total identification, not an adjunction theorem. The internal action-site presentation supplies the small ringed site and the restriction m to a f*m. The general module-sheaf closedness statement supplies closed symmetric tensor; the independent-coefficient flat-resolution statement applies to both small sites in the coefficient universe. I read Stacks sites-modules.tex, Tag 03EO / lemma-internal-hom-adjoint-tensor, and Tags 03EV / lemma-j-shriek-flat and 03EW / lemma-module-quotient-flat, as well as the free-presheaf-cover declaration hasFunctorialFlatResolution_kfi in lean/Sheaf/Algebra/Homology/KFlatResolutionIndependentCoefficients.lean, lines 473 onward. Local balanced tensor maps, followed by sheafification, give the diagonal restriction formula. There is no assumed pointwise exactness of sheaf cokernels.

Step 2 is elementary: flatness follows by applying exact conservative forgetting to a short exact sequence, identifying its underlying tensor, then using the definition of flatness. The same acyclic-tensor test on total complexes proves preservation of K-flatness. No claim that exact strong monoidal functors generally preserve all flat objects is invoked. The source and target tensors have already been identified in step 1.

Step 3 uses the precise counit/computation-unit equation from lem-trf-bounded-below-derived-adjunction. I read PlusAdjunction.lean lines 130-160 and Stacks derived.tex Tag 0DVC / lemma-pre-derived-adjoint-functors (and its general predecessor). The action infrastructure supplies bounded-below injective resolutions and invertibility of the computation unit on them. The ordinary counit is the invariant inclusion by the normalized transpose, not just by the abstract existence of an adjoint. The lattice-derived-invariants definition fixes exactly that computation-unit-preserving adjunction, so the two presentations agree.

Step 4 uses the full cubical statement: natural chain maps, quasi-isomorphism of augmentation on EVERY complex, and E composed with tb tensor identity equal to invariant inclusion composed with augmentation. Naturality of augmentation provides the second square explicitly. Cancel both augmentation denominators first, then cancel Q(tb_J), which is invertible because the injective-normalization statement says b_J is a quasi-isomorphism and identifies lambda_J with its inverse. The domain is D(t)QK(J), the target is QJ, and no cohomology-level substitute is used.

Step 5 uses the infrastructure only for the bounded-below injective resolution P to J. It uses the cubical statement for naturality and injective normalization for lambda_P = lambda_J Q(Ks). I wrote both resulting equations with target QJ and canceled Qs. There is no implicit compatibility assertion standing in place of this calculation.

Step 6 uses the generic derived tensor comparison after checking every hypothesis in steps 1 and 2. The exact-functor factorization node is a Mathlib leaf and explicitly says no resolution is needed, so it identifies the exact presentation used here. I read Stacks sites-cohomology.tex Tag 07A4 / lemma-pullback-tensor-product, whose flat-term K-flat representative calculation motivates the normalization; the generic statement, rather than a geometric special case, is the cited tool. The lattice definition fixes the same normalized tensor and regular unit. Tensoring equality of two derived morphisms is elementary functoriality and is explicitly distinguished from tensoring arbitrary ordinary roofs without replacements.

Step 7 uses the condensed cup-coherence statement for its exact tensor-of-counits transpose and unit transpose, and the restriction-calculus statement for the named regular-coefficient cup. The lattice tensor definition makes precisely those same choices. The internal/section comparison fixes tensors and regular units, so equality follows by injectivity of the adjunction bijection. This does not assume a theorem about cup products from a definition of invariants alone.

I checked r=0 using the identity clauses of the cubical and injective-normalization statements; the zero ring and zero complex yield zero objects and the same equations; all other arguments allow arbitrary characteristic, nonflat modules and positive lattice rank. The total is finite in Koszul degree, and resolutions remain bounded below. Every cited statement applies with the actual coefficient category and its fixed universe. I checked graph reachability of the generic tools and found no path back to the item. All steps have fewer than 2000 characters, and no new clause node conceals the argument. All citations are verbatim copies of the actual statements. I reviewed delivery-errors B-E: no statement-only new-node rules arise, the non-elementary comparisons have cited statements, the proof performs the cancellation rather than relabeling the item, and no extra hypothesis has been introduced.

## Repair of the landing refusal (2026-10-23)

The return says that the reader approved the split but the side-project completion had never been promoted to the live DAG. I compared the retained delivery (dry-run head 6a8b94b5e88) with the current read clone: the live item is unsplit, with empty proof and proof dependencies, and has no released repair note. Its statement and statement dependencies are exactly those of the retained split. I rebuilt the sandbox item from that current node, overlaying only stage-1 proof, search and blueprint-reference fields, so current metadata is preserved. The required delivery command constructs its commit on current origin/sheaf-dag; promotion and acceptance remain the maintainer's work.

I re-read all thirteen current proof dependencies. Each complete statement is still identical to its retained verbatim citation in citations.json, so no citation has been silently redirected or weakened. This covers the action injective infrastructure, internal/section tensor comparison, action-site presentation, closed sheaf-module tensor, functorial flat resolutions, bounded-below derived adjunction, normalized lattice tensor definition, cubical evaluation, injective normalization, derived tensor comparison, exact derived factorization, cup-mate coherence and restriction calculus. Current completion metadata on those dependencies is not substituted for their statements. The current Lean search for the item tag and cubical/lattice-counit notions found no exact project declaration, so there is no attachment.

The mathematical edit is in step 1. The current action-site presentation uses a generated Grothendieck topology and expressly does not assert composition for its displayed precoverage. Its last paragraph identifies action-site module sheafification with base-site sheafification carrying the induced action. I now invoke that precise clause on the balanced tensor presheaf to justify the diagonal tensor identification. Closedness and flat resolutions require a small ringed site, not finite limits on this action category, and no stronger precoverage axiom is used. This keeps the approved route while making its use of the current presentation explicit.

For steps 2–7 I checked the same actual hypotheses again: exact conservative forgetting detects the flatness and acyclicity tests; the computation-unit counit equation is applied to the specified exact left adjoint; both augmentation maps and the injective comparison are invertible before cancellation; the tensor comparison is used on flat-term K-flat representatives; and the cup maps agree by their specified adjunction transposes. Rank zero, zero coefficients and nonflat inputs introduce no extra assumption. Every step remains under 2000 characters. Existing proof, citations, WANTED reference and genuine search records are retained; no new search is asserted and no new node is introduced.

## Unfinished work

No part of this stage-1 split remains unfinished. The existing unsplit dependencies remain separate DAG items; no Lean was written and no compiler, Lake or build was run.
