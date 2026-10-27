# Worker report: lem-sfb-sheaf-dg-hflat-computation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-dg-hflat-computation.json`: item split, statement unchanged; eight proof steps constructing the resolution and proving the canonical comparison.
- `dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-dg-free-graded-flat.json`: statement, unsplit; no Mathlib match. Free generators are a graded sheaf of sets, not a fixed set of global sections.
- Reused live `lem-sfb-sheaf-dg-homotopy-system`; removed the draft homotopy/acyclic node after the push duplicate gate detected the concurrent landing.
- `citations.json`: a verbatim statement excerpt (in this delivery the whole statement) for every node cited in every proof step.
- `searches.jsonl`: actual msearch records, retained unmodified. No Lean was written or compiled.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact item tag and the homotopically-flat, sheaf-dg and graded-flat concepts. No declaration states this item or either new input. Existing K-flat ordinary-complex files do not handle modules over a sheaf of possibly nonzero-differential dg algebras.

## WANTED

None. All mathematical sources used are in `literature/stacks-project/`.

## Corrections and scope

No statement correction was needed. The starting item was unsplit and had no proof. Its previous Mathlib searches were preserved, with fresh searches appended rather than silently overwritten. There was no prior sandbox split, report or search log to resume.

The precise source is `sdga.tex`: Tag 0FSH, `lemma-resolve`, FIRST proof (local cycle generators, successive boundary killing, filtered colimit); Tag 0FSI, `lemma-acyclic-good`, proof (1); Tag 0FTF, `lemma-derived-tensor-product`. Conditions (1) and (2) of good modules are sufficient here; universal stability under arbitrary geometric base change is not needed. In particular I did not invoke ordinary commutative-ring K-flatness as though it were the sheaf-dg statement.

The first new node is the independent free-cell input, Tags 0FSF (`remark-sheaf-graded-sets`) and 0FSG (`lemma-free-graded-module-good`). I wrote the graded family and differential explicitly and retained only graded flatness and tensor acyclicity. The source's right-module convention becomes the displayed left convention via graded opposites. The source has a typographical 'differential graded A-algebra'; the actual ringed-site datum is a dg O-algebra and is written so here.

The second new node uses Tag 0FS7 (`proposition-homotopy-category-triangulated`) and the cohomological cone criterion of Tag 0FT4 (`lemma-qis` and proof). It supplies the SHEAF dg homotopy category, not its scalar adjunction. The already existing generic triangulated cone-class theorem supplies the fraction calculus in step 7, so no second cone-class or general derived-computation node was created.

I read the chapter and unit JSON records, SETUP's three levels and GOAL, and the latest blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, particularly `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. This item's inherited prerequisite concerns the scalar models below the direct-image clause. It is not the key statement of that unit, so the unit realization fields are not ours to populate. `blueprint_refs.py ancestor` reports a null nearest imported ancestor; the existing null ancestor and full via chain are retained and extended for the new nodes. Whole-blueprint searches for homotopically flat, free graded module, graded sets, sheaf dg, graded sheaf, 0FSG, 0FS7 and 0FT4 found no matching blueprint statement. Ordinary-complex and countable ring-DG matches were read and rejected as below.

## Mathlib searches

The fifteen fresh searches were run only through the prescribed msearch command and their actual summary outputs are in `searches.jsonl`. Each new node has LeanFinder in two phrasings, Loogle, grep and LeanSearch records with the exact queries and results. Both search services answered; there is no unavailable service recorded as an absence.

For the free-cell input I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean:41` (free module on a constant type), `Algebra/Category/ModuleCat/Presheaf/Free.lean:43` (ungraded presheaf free object), and the ordinary flat-module search candidates. These do not give tensor acyclicity for a free dg sheaf module on varying local graded generators. The second phrasing returned HasGoodTensor instances about monoidal colimit/associativity hypotheses, not K-flatness, and IsKProjective for ordinary complexes (`Algebra/Homology/HomotopyCategory/KProjective.lean:31` onward).

For the homotopy/acyclic input I read `Mathlib/Algebra/Homology/DerivedCategory/Fractions.lean:34` and `:38`: these are instances for ordinary cochain complexes in an abelian category. `Algebra/Homology/DifferentialObject.lean:12` onward describes the complex/differential-object equivalence without a sheaf dg algebra action. General triangulated cone localization is already represented by an existing Mathlib DAG leaf and is reused. The item searches likewise returned Tor, ordinary projective resolutions and ordinary-module exact tensor criteria, not the unbounded sheaf-dg resolution/comparison.

## Not duplicates

lem-sfb-sheaf-dg-homotopy-acyclic vs lem-sfb-ringed-dg-scalar-adjunction: the existing node states triangulation of the localized derived categories and derived scalar extension/restriction adjunction, but not triangulation of K_X(A), its full acyclic subcategory, or the cone criterion there; these are the new input. Its source includes 0FT4 but its statement does not supply this input.

lem-sfb-sheaf-dg-homotopy-acyclic vs lem-sfb-dg-coefficient-realization-comparison: the existing node compares normalized scheme coefficient realization arrows under base change; it does not state the homotopy category or the acyclic subcategory for an arbitrary sheaf dg algebra. Its source mentions 0FT4 as part of that different comparison route.

lem-sfb-sheaf-dg-homotopy-acyclic vs lem-sfb-dg-homotopy-acyclic-localization: the existing node concerns a single dg ring over Z and modules of abelian groups, not module sheaves over a sheaf dg O-algebra on an arbitrary space. Passing between these objects is not a one-line specialization.

lem-sfb-sheaf-dg-homotopy-acyclic vs lem-sfb-dg-quasi-isomorphism-localization: the existing node again concerns ordinary dg rings and adds opposite localizations, not sheaf dg module homotopy categories.

lem-sfb-sheaf-dg-free-graded-flat vs lem-sfb-dg-countable-free-cover: the existing node assumes a countable ordinary dg ring and countable module and constructs a two-layer cover; the new statement concerns free modules on arbitrary graded sheaves of sets and asserts their exact tensor property and dg tensor acyclicity.

lem-sfb-sheaf-dg-free-graded-flat vs lem-sfb-dg-countable-semi-free-resolution: the existing node is a countable ordinary ring-module resolution, not the free graded SHEAF cell flatness statement. No existing DAG node contains 0FSF or 0FSG at the audit time.

Neither new node states a clause of the item: one gives the free cells used to construct a resolution and the other gives the ambient homotopy calculus. Neither asserts existence of flat resolutions of arbitrary modules or that those resolutions compute scalar extension. Those arguments remain in the item's steps.

## Review by Q16

I reviewed B--E with the source statements, their proofs and every cited DAG statement open. The two new statements introduce all objects, give the module and tensor conventions through actual defining nodes, use TeX with single mathematical backslashes, and carry no proof or proof dependencies. All fresh searches were actually run, and their nearest blueprint provenance was checked. Sources use the Stacks tags AND labels. There are no claims of a Mathlib leaf without a declaration or a verified line.

Step 1 cites the actual balanced tensor, left action, shift and cone definitions, and the degreewise-short-exact-complex cohomology sequence. I checked both signs: tensoring in the second variable multiplies the shifted coordinate by (-1)^|t|, whereas tensoring a right-module cone in the first variable needs no extra sign. This proves the equivalence with preservation of quasi-isomorphisms. This is a direct two-summand calculation, so elementary is appropriate.

Step 2 takes graded flatness AND tensor acyclicity from the new free-cell statement, which says both. The generators are local sections of the kernel SHEAF, so no surjectivity of global sections or lifting of cycles over an entire open is assumed. It is the initial step of the actual resolution construction, not a citation of a new resolution theorem.

Step 3 uses the same free-cell statement for the quotient and the general complex short-exact-sequence theorem for the tensor sequence. The splitting is only in graded modules, which suffices to give a split exact sequence degree by degree AFTER balanced tensor. The differential of each new generator equals its selected old cycle; h_i(p)=dm is exactly what makes the extension a dg map. The induction starts at P_0, and no boundedness or O-flatness enters. Kernel killing is not assumed until the explicit next-stage attachment.

Step 4 uses the existing theorem that filtered colimits of abelian sheaves are exact. This is sufficient for modules: underlying colimits get their actions and differentials from the compatible structure maps; finite kernels/images can be checked underneath, and tensor commutes with the colimit by its balanced-map universal property. I wrote these transfers out rather than citing a definition of colimit for an exactness theorem. The local representative of a cohomology kernel class has h_i(p)=dm after restriction, hence is killed by exactly its (p,m) generator. All degrees are treated simultaneously. I also checked the opposite multiplication and Koszul action so this construction supplies right-module resolutions when step 5 needs them.

Step 5 uses the already constructed right resolution, with an acyclic left C. I checked the two different acyclicity hypotheses separately: R's right tensor property applies to C, while C's left tensor property applies to the cone of R to N. The actual cohomology-sequence node gives the inference for the tensor cone. No statement about arbitrary tensors of acyclic complexes is assumed; that would be false. This short application of previous steps and the cited cohomology sequence is elementary.

Step 6 uses the new SHEAF homotopy cone criterion, not the ordinary-DG-ring localization node. The cone of a map between members of P is graded-flat because it is the graded sum of the two shifted members; its homotopical flatness follows from the explicit tensor cone and cohomology sequence. The acyclic case just proved applies with N=B regardless of O-flatness. This proves preservation of quasi-isomorphisms on the resolving class by the actual ordinary scalar functor.

Step 7 is where the categorical computation criterion is used. I reread all five cited statements: the new node gives the triangulated homotopy category and full replete acyclic triangulated subcategory; lem-trf-triangulated-subcategory-cone-system gives the right calculus of fractions for exactly that cone class; lem-pur-resolving-class-essential-constancy requires just that calculus, two-out-of-three, existence of resolutions and inversion between representatives, all established here. Its statement explicitly makes the identity leg invertible on P. The pointwise-Kan bridge applies to arbitrary categories with a right multiplicative system, not only ordinary complexes, and explicitly identifies its comparison with that identity leg. Finally lem-sfb-pointwise-right-kan-from-limits assembles exactly these limit cones and states the universal natural-transformation bijection. This avoids the tempting but invalid citation of lem-pur-left-derived-from-kflat-class, whose source category is restricted to ordinary complexes in an abelian category. These generic categorical tools are declared in split_report.tool_uses where needed.

Step 8 uses the scalar-adjunction node only for existence of the designated universal pair, which its statement gives also for LEFT modules via opposite algebras. The definition of derived extension supplies the universal property and comparison. The two universal-property maps are inverse by uniqueness; naturality is the displayed equation of that actual comparison, not an asserted agreement of arbitrary derived isomorphisms.

Small-case checks: X empty gives zero module sheaves and vacuous exactness. An empty graded generating sheaf gives the zero free dg module. M=0 admits the zero resolution (the construction may also produce a nonzero acyclic representative, which is harmless). Degree-zero nonflat coefficient rings and nonflat algebra maps are allowed: only graded A-flatness, never O-flatness of A or B, was used. Nonzero differentials and negative generator degrees obey the displayed Leibniz signs; the construction indexes all integer degrees and its stage index alone is N. No convergence of an unbounded spectral sequence, infinite product exactness, countability of sections, or global cycle lifting is used. All proof steps are under 2000 characters; none hides a separate comparison theorem inline.

The substantive corrections during my own review were to avoid treating the ordinary-complex derived-computation theorem as a sheaf-dg theorem, to separate the two uses of homotopical flatness in the acyclic tensor argument, and to write the exact comparison identity after identifying universal pairs. No source statement of the item was weakened.

## Unfinished work

The two new inputs are deliberately statement-only, as required by a one-level split. No part of the item's natural-language argument is left unfinished. The independent mathematical review is the maintainer's; this is the author's signed self-review.

## Final live-state duplicate repair

The dry run passed at 39a5bb8bdfc, but the subsequent push gate found the newly landed `lem-sfb-sheaf-dg-homotopy-system` from group NQ. I opened its complete statement: it states the sheaf dg homotopy triangulation, both fraction calculi, two-out-of-three, and the acyclic-cone criterion. I therefore removed my draft `lem-sfb-sheaf-dg-homotopy-acyclic` entirely and repointed steps 6 and 7 to the existing node. Step 7 now uses its fraction calculus directly, so the separate generic cone-system citation is also removed. The detailed source review above records the work on the superseded draft; the final delivery has ONE new node, free-graded-flat. The live right-module assertion specializes via the graded opposite to precisely the left-module convention (including the shifted action). I regenerated every citation quote from the final live statements and retained all actual searches. This is a duplicate repair, not a change of the mathematical route or statement.
