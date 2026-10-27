# Q60 stage-1 report: lem-sf-adic-module-slice-hom-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-sf-adic-module-slice-hom-comparison.json`: statement, split into eight proof steps; Mathlib searches found no matching declaration for the complete comparison.
- `citations.json`: one verbatim statement quotation for every node cited by each proof step.
- `report.md`: this report. `searches.jsonl` is the unmodified output log of the required search command; `write_split.py` is a sandbox-only preparation script.

There are **0 new nodes and 0 new Mathlib leaves**. The non-elementary inputs already have nodes. In particular, neither an abelian-sheaf comparison specialized to the wrong ambient category nor a new node restating a clause of this item is used.

## Attachments

None. Searching the project source under `lean/WeilConjectures/` for the blueprint tag, sectionwise modules, slice Hom and proposed equivalence names found no declaration stating this complete item. The existing native definitions and results in `SixFunctors/ProEtale/Adic/Module.lean`, `Hom.lean`, `InternalHom.lean` and `InternalHomEvaluation.lean` provide native module operations, equalizer Hom and pullback compatibility; they do not identify those operations with the sectionwise module-sheaf presentation. Thus they are source material, not an attachment.

## WANTED

None. All literature used is available in the read clone.

## Problems found and changes

The item was unsplit and had no proof. Its statement is retained verbatim. It requires the native ambient category of **K-vector-space sheaves**, not merely internal modules in abelian sheaves. I wrote the action comparison directly using K-bilinear maps and the sheafification universal property, and checked that restriction along constants recovers the original K-action. This is why `def-weil-pbc-internal-abelian-sheaf-module-equivalence` and `lem-pe-internal-section-tensor-comparison` are not cited as if they immediately applied to the native category.

No repair note exists for this item. There was no earlier sandbox node, report, citations file or searches log to reuse. Existing item search records were preserved; five actual Q60 searches were added, including two semantic phrasings. The LeanFinder hits were sectionwise `SheafOfModules` constructions, a light-condensed internal Hom, and ordinary module evaluation. LeanSearch also gave sectionwise module categories. Loogle returned no hits. The grep hit in `Mathlib/CategoryTheory/Monoidal/Internal/FunctorCategory.lean:23` is a motivating comment: the file constructs monoid objects in a presheaf category, not modules in sheaves with the required comparison. I read that file. None proves this item in one specialization.

The existing `blueprint.from.node` is null: the ancestor tool explicitly returns null through the maintainer-created ancestry. Its informative `from.place` and `via` were preserved, and the split report identifies the finite-free, bidual-evaluation and locality sentences of the actual blueprint proof. `blueprint_refs.py search` was run for module, slice Hom, native adic and internal module; there is no blueprint node stating the complete native adic comparison. The item is an ancillary technical comparison, not the key node of its recorded unit, so no unit realization record is changed.

## Not duplicates

No new node is proposed. The existing abelian internal-module equivalence and tensor comparison were examined and not duplicated; they concern tensor over Z in abelian sheaves. Generic sheaf tensor closure, the tensor--slice-Hom adjunction, normalized uniqueness of right adjoints, slice tensor restriction and pro-etale localization are cited through their existing nodes. No declaration of Mathlib is being called an attachment of the project.

## Review by Q60

I read `GOAL.md`, the worker brief, the three-level rules in SETUP, the chapter and unit records, and delivery-errors B--E. For the mathematical source I read Stacks `sites-modules.tex`, the tensor product construction and its balanced-bilinear universal property (03EK), sheafification/tensor compatibility (0GMW), tensor pullback (03EL), the definition of slice Hom and evaluation, its restriction lemma (0E8H), and the tensor--Hom adjunction (03EO). I also read `sites.tex`'s localization-with-products statement and proof (03CE). The native Lean modules named above fix which native operations are compared. The blueprint `lem-sf-hom-finite-projective.proof.md` explains why the finite-free/bidual/locality normalizations matter here. The comparison argument itself is marked agent-written rather than attributed verbatim to Stacks.

Step 1 uses `def-weil-pbc-sheafification`, which actually states unique extension into a sheaf, and `lem-weil-pbc-sheaf-tensor-closed`, whose statement includes sheafified sectionwise tensor and strong monoidality of sheafification. I apply that node with the Grothendieck abelian symmetric monoidal closed category of K-vector spaces, not with an arbitrary tensor or a different scalar field. The native ambient tensor in the item is exactly this tensor. Its strong monoidality permits testing the associative action diagram on the presheaf triple tensor. This proves the action correspondence rather than assuming an equivalence of two module presentations.

Step 2 uses the definition of sectionwise module sheaves and the uniqueness from sheafification. I checked that an R-linear map is K-linear via constant functions and that the converse internal morphism condition is exactly R-linearity on sections. The equation gamma(c1,m)=c gamma(1,m)=cm is necessary: leaving it out would not show that the inverse equivalence preserves the given K-vector-space structure. Identities, compositions, inverse equivalence maps and the regular module are then literal sectionwise identities. This step is elementary relative to step 1 and the cited definitions.

Step 3 uses the sheafification universal property and the actual sheaf tensor definition, not a definition of flatness or any unstated preservation theorem. The native coequalizer tests are expanded as the balanced and output-linearity equations. Conversely those two equations recover R-bilinearity. The two representing maps are constructed from the same pairing and the inverse identities are checked on it. The comparison is thus pinned by pure tensors; no tensor identification is claimed without specifying its maps. No flatness or finite-generation hypothesis is used.

Step 4 uses `lem-pc-sheaf-modules-tensor-closed`, whose statement explicitly gives the slice-Hom adjunction for arbitrary ringed sites and arbitrary module sheaves. `det-sp-unique-right-adjoint` explicitly gives both the natural isomorphism and its counit identity, so it suffices to identify evaluations as well as objects. `def-pur-sheaf-hom` gives maps on the entire localized site, not Hom of section modules at a single object. Reading those statements prevents confusing a sectionwise Hom module with a slice Hom sheaf. I checked the scalar/output conventions and the symmetry when native evaluation is written Hom first. Bidual evaluation is its transpose; invertibility for arbitrary modules is neither used nor claimed.

Step 5 uses clause (1) of `lem-weil-proetale-weakly-etale-localization` for the site equivalence and covering comparison, and clause (1) of `lem-sfb-proetale-object-inverse-image-restriction` for the **actual** inverse-image functor, its initial indexing object and its natural sectionwise identification. Both statements allow any object of the small pro-etale site; this is not restricted to open or finite-etale objects. The constant-ring clause of the latter is not misused for the non-discrete function ring R: identity of R's structural map is proved separately by pulling functions along the identity of each further object V. All smallness hypotheses hold by the size convention already in the item's statement.

Step 6 applies `lem-sfb-localized-site-tensor-restriction` first over the constant ring K; its statement explicitly pins the comparison by pure tensors and imposes no flatness condition. Together with step 5 it computes the monoidal pullback action on sections. The two maps for extension of scalars along the identity are written, and the balanced relation verifies their inverse identities. `def-pur-localized-ringed-site` states the exact sectionwise restriction formula, so it really gives the restriction being compared.

Step 7 uses the same tensor-restriction theorem over R, not only over K. For Hom, the definition node and the relocalization clause of `def-pur-localized-ringed-site` suffice: the two values at V/U are literally the same maps on C/V. Thus 0E8H is proved here in a short step, not turned into a new node. Evaluation commutes because its value on m,lambda is the same lambda_V(m). The actual native comparison is characterized as the transpose of evaluation, so the counit-preserving uniqueness node checks the map, not just its endpoints. Successive restrictions are identities on the same localized maps.

Step 8 uses the sectionwise module category definition and the preceding equivalence. The finite-product module with coordinate inclusions and projections satisfies the biproduct equations sectionwise, including the empty sum. Thus the equivalence carries a finite free object and both inverse trivialization maps to exactly their counterparts. This small calculation is a step, not an extra lemma node.

I checked small cases: the empty scheme and empty site object; the zero module; rank zero; the regular rank-one module; arbitrary non-finite modules for which bidual evaluation need not be invertible; and a site-object morphism that is not an open immersion. No finite-type, quasi-compactness, Noetherian, finite-dimensionality of a module, or lisse assumption is inserted. The local finite-dimensional-span condition on coefficient functions survives unchanged because it is a condition on the same topological space |V| on both sites. Constants and products of coefficient functions remain in the ring (locally take finite spans and their finite products), so the scalar actions used in the comparison are meaningful.

I checked every cited node's statement and copied the relevant statement into citations.json verbatim. None of the steps relies on a proof-only construction of a cited node. All non-elementary steps are supported by those statements. Every step is below 2000 characters; none hides a separate standard comparison lemma. No new unsplit node, restatement of the item, circular use, unsupported Stacks citation, or forbidden SGA source is introduced. The generic off-unit tool uses are declared in split_report with their purposes; they do not replace any geometric step of the unit.

## Unfinished work

None at stage 1. No Lean files were written and no compiler, Lake or build command was run. Required server validation and delivery follow this report.
