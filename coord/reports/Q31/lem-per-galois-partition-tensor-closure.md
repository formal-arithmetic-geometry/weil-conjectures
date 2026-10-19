# Worker report — Q31

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-galois-partition-tensor-closure.json: item, split, statement unchanged, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-local-system-tensor-monodromy.json: new statement-only lemma, unsplit, no Mathlib match.

No Lean files were written and no compiler was run. The chapter and unit records were read and left alone: this auxiliary node is not the unit's key statement. citations.json contains a verbatim statement excerpt for every proof citation. Searches were run through msearch.py and searches.jsonl retains the actual answers; old searches in the imported item are retained.

## Attachments

None. Searches in WeilConjectures for the exact blueprint id and for Galois partition, ind-unipotence and local-system monodromy found no project declaration proving the item. Representation.tprod is a Mathlib representation construction, not an etale sheaf comparison. The finished tensorObj_part theorem covers local constancy only and does not prove this item.

## WANTED

None. The ILO PDF and the Stacks sources used here are present locally.

## Findings and route

The item is true as stated. It has arbitrary module values and asserts ordinary tensor closure without flatness; replacing its graded pieces by tensors of graded pieces would be unjustified. The proof instead uses images for its convolution filtration and checks the action on those images explicitly. The source is ILO Expose XVII, 7.2.1–7.2.5, Definitions 7.3.2–7.3.3 (printed pp. 301–304), and its application in Lemma 7.6.11 (p. 314). I read these passages and the main-20261015 blueprint ancestor's Step 3. This is an auxiliary argument in the inherited coefficient-duality branch of that step, not a change to the chapter or unit route.

A genuinely missing comparison has been isolated: the existing monodromy node states exactness, colimits, constant pullbacks and descent, but does not assert that ordinary tensor is sent to diagonal tensor. The new node supplies that general comparison for arbitrary torsion local systems, without mentioning a fixed partition or ind-unipotence. Its underlying argument, to guide the next worker, uses ILO 7.2.3's identification with the classifying topos: tensor is built from finite products, free-module constructions and colimits, and ILO 7.2.4 says that inclusion of local systems preserves the necessary finite limits and colimits. Thus inclusion preserves the bilinear universal construction of tensor. The stalk functor gives diagonal action on pure tensors. This is not an inference from the finite-stalk equivalence. Stacks 03EL and the bilinear characterization just before lemma-tensor-product-pullback (sites-modules.tex:3649), and 0GMW lemma-sheafification-tensor (3606), give the intrinsic tensor and constant-coefficient identifications.

## Not duplicates

lem-per-local-system-tensor-monodromy vs lem-per-torsion-local-system-monodromy: the existing node supplies the exact additive monodromy equivalence, descent and colimits, but has no tensor clause.

lem-per-local-system-tensor-monodromy vs cor-galois-lisse-representations: that tensor equivalence is restricted to finite rings and finite stalks, or to adic finite-rank coefficients; the new node permits arbitrary torsion rings and arbitrary discrete stalk modules.

lem-per-local-system-tensor-monodromy vs lem-pod-lisse-tensor-and-scalar-extension: the existing tensor/lissity clause assumes a finite coefficient ring and finite stalks; it does not give arbitrary ind-finite local-system closure or monodromy equivariance.

lem-per-local-system-tensor-monodromy vs lem-pod-etale-stalk-tensor-scalar: the existing lemma compares stalk tensors of arbitrary sheaves, but does not assert that their tensor is an ind-finite local system or identify its fundamental-group action.

lem-per-local-system-tensor-monodromy vs lem-per-galois-cover-module-descent: the existing node handles constant pullbacks along a single finite cover and a scalar tensor with a trivial first factor; the new node also handles local systems that are not trivialized by any single finite cover and tensors with both actions nontrivial.

lem-per-local-system-tensor-monodromy vs lem-weil-pbc-ringed-topoi-module-pullback-tensor: 03EL for arbitrary ringed-topos pullback gives neither membership in the ind-finite local-system category nor a fundamental-group action.

lem-per-local-system-tensor-monodromy vs lem-pc-sites-module-sheafification-tensor: 0GMW compares presheaf and sheaf tensor; it does not state the local-system tensor comparison or its equivariance.

lem-per-local-system-tensor-monodromy vs lem-weil-pbc-sheaf-tensor-closed: that generic theorem constructs the tensor on all coefficient-valued sheaves and proves cocontinuity, without the etale local-system subcategory or fundamental-group comparison.

The whole DAG and both blueprint snapshots were searched for local systems, tensor, monodromy and source place 7.2.3. blueprint_refs.py found no blueprint statement for this comparison. The locally-constant tensor node and derived finite-type tensor node also lack the claimed arbitrary ind-finite comparison. New-node Mathlib searches use two semantic phrasings, LeanSearch, Loogle Representation.tprod and a grep in AlgebraicGeometry. I read RepresentationTheory/Basic.lean:624–633: its ordinary representation tensor gives no etale comparison. Other hits concern condensed sheaves. There is no one-line Mathlib specialization.

lem-per-local-system-tensor-monodromy vs lem-sfb-site-inverse-image-bilinear-adjunction: the existing statement is a formula for bilinear adjunction under a geometric morphism; it does not assert tensor closure of ind-finite etale local systems or identify monodromy.

lem-per-local-system-tensor-monodromy vs def-weil-pbc-canonical-ringed-tensor-comparison: the existing node defines normalized tensor-comparison data for a ringed inverse image; it has no local-system tensor closure assertion.

lem-per-local-system-tensor-monodromy vs def-weil-pbc-ringed-tensor-square-presentation: the existing node defines a derived ringed square presentation and its normalization, not the ind-finite etale subcategory and its tensor.

lem-per-local-system-tensor-monodromy vs lem-weil-pbc-algebraic-inverse-image-pairing-isIso: the existing assertion makes a supplied transported bilinear pairing invertible; it does not place ordinary etale tensors inside local systems.

lem-per-local-system-tensor-monodromy vs lem-weil-pbc-algebraic-inverse-image-pure-pairing: the existing assertion constructs the inverse-image bilinear pairing and its pure-section formula; it does not compare etale local systems with fundamental-group modules.

lem-per-local-system-tensor-monodromy vs lem-weil-pbc-algebraic-inverse-image-tensor-comparison: the existing node gives the natural geometric inverse-image tensor comparison; it does not assert closure of the ind-finite local-system subcategory.

lem-per-local-system-tensor-monodromy vs lem-weil-pbc-canonical-ringed-tensor-comparison-construction: the existing node constructs normalized ringed tensor-comparison data; it contains no local-system membership or monodromy assertion.

lem-per-local-system-tensor-monodromy vs lem-weil-pbc-continuous-module-encoding-lattices: the existing statement concerns finite locally free lattices under continuous condensed E-coefficient encoding, rather than arbitrary torsion etale local systems.

lem-per-local-system-tensor-monodromy vs lem-weil-pbc-continuous-module-encoding-restriction: the existing statement concerns restriction of internal continuous coefficient encodings under etale or weakly etale maps, not diagonal tensor monodromy for torsion local systems.

lem-per-local-system-tensor-monodromy vs lem-weil-pbc-continuous-module-encoding-scalar-extension: the existing statement compares continuous integral-to-field scalar extension with its encoding; it is not an arbitrary torsion local-system tensor comparison.

## Review by Q31

The first dry run requested ten additional 03EL comparisons. I opened all ten node statements, found only inverse-image tensor constructions or continuous-coefficient encoding assertions, and added a separate comparison for each under Not duplicates. I read ILO XVII 7.2.1–7.2.5 and 7.3.1–7.3.4 against the item and new node, and sites-modules.tex 0GMW/03EL and the bilinear characterization, plus the 03EO internal-Hom tensor adjunction. The local-system definition is specifically ind-finite etale, as ILO 7.2.1 requires: etale-locally constant sheaves of infinite values alone are not silently identified with local systems. Descent along the chosen finite surjective cover, followed by torsion-extension closure, justifies that identification for the finite-filtered terms used here.

Step 1 uses exactly the constant-ring identification and exact inverse image in lem-pe-constant-left-module-inverse-image, and the underived tensor pullback isomorphism in lem-weil-pbc-ringed-topoi-module-pullback-tensor. The stratum morphism need not be etale: both tools apply to its geometric morphism. Constant coefficient rings identify the ringed pullback with the restriction in the statement.

Step 2 uses the statement of lem-per-torsion-local-system-monodromy, which I opened in full: its finite-cover descent, ambient torsion-extension closure, exact equivalence, colimits, and pullback-constant criterion say precisely what this step takes. The hypotheses hold on each nonempty connected Noetherian stratum, and ell A=0. No finite generation is required and no use is made of its finite-type clause. A local system with trivial H-action pulls back to a constant sheaf on V, and that actual etale cover witnesses local constancy of each quotient.

Step 3 uses the new general tensor comparison and the generating pure tensors of def-weil-pbc-module-tensor-product. I checked the identity (h-1)(u tensor w)=(hu-u) tensor hw+u tensor (hw-w), all indices, stability, and both endpoint filtrations. This is the short elementary action calculation, not a hidden flat associated-graded theorem. It does not need H normal, so no Galois subgroup-normality result is hidden here. The finite cover in Step 2 still supplies the H-action and its constant-pullback criterion.

Step 4 uses only the exactness and pullback assertions of the same monodromy node. It transports an actual finite filtration, with quotients computed in ambient sheaves, back from modules. It does not claim that arbitrary etale subsheaves of a constant sheaf are local systems, an assertion that would be false.

Step 5 uses the complete statement of lem-weil-pbc-sheaf-tensor-closed: Mod_A is the usual Grothendieck abelian closed symmetric monoidal module category, tensor is additive, and the small etale site has an essentially small model in the coefficient universe. Its all-colimits assertion therefore applies. The statement of lem-pc-sites-module-sheafification-tensor with O the constant presheaf A identifies the sheafified objectwise A-tensor with tensor over A_S, so these are the same ordinary tensors as the item. The two index categories are small and filtered by their original presentations, and their product has these properties coordinatewise. No unbounded or large colimit is substituted for a small one.

Step 6 is precisely the definition of the class on the fixed finite list of strata. I checked empty X, zero modules, length-zero filtrations, the identity cover and a point, infinite-rank constant values, A=F_ell[epsilon]/epsilon^2 and nonflat modules A/(epsilon), and nontrivial finite unipotent representations in characteristic ell. The image construction and action identity survive each case. The new node also includes the zero ring (n=1) and is consistent with tensor of constant sheaves and finite-stalk specializations.

I checked delivery-errors B–E: the new statement introduces every object and has no proof or proof sketch in its statement, proof or proof_deps; its notion nodes are cited. Every non-elementary comparison used by the item is in a cited node's statement, with verbatim excerpts in citations.json. The new lemma is independent of partitions and unipotent filtrations, so it is strictly smaller rather than an item's clause relabelled. All item steps are under 2000 characters. No SGA source is cited. No statement correction or source dispute was necessary. Generic off-unit site/tensor tools are declared in split_report.tool_uses.

## Unfinished work

None for this stage-1 split. The new statement-only node is intentionally unsplit, as the one-level delivery requires.
