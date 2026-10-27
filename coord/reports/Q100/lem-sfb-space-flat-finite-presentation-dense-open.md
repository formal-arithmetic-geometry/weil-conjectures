# Q100 stage-1 delivery: lem-sfb-space-flat-finite-presentation-dense-open

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-finite-presentation-dense-open.json`: item, statement, now split in six steps. No new nodes; no new Mathlib leaves. The statement and its statement dependencies are unchanged.
- `citations.json`: 24 entries, one for every step/node citation, quoting the existing node's statement verbatim.
- `report.md`: this report. `searches.jsonl` contains the actual msearch output records. `prepare.py` is sandbox-only preparation material, not a project file.

## Attachments

None. Searched the read-only project `lean/WeilConjectures/` for the exact blueprint tag, 0877, schematic density, finite presentation over a dense open, and related flat finite-presentation declarations. The generic-flatness and GenericFlatFinitePresentation modules concern shrinking an integral base, not extension across the boundary of a specified schematically dense open; they do not attach this item. No Lean was written and no compiler, Lake or build command was run.

## WANTED

None. All proof sources used are present locally.

## Findings and corrections

The source statement is correct and is kept verbatim. Stacks `spaces-more-morphisms.tex`, Tag 0877, label `lemma-flat-finite-type-finitely-presented-over-dense-open-X`, has exactly the three hypotheses in the item and no separatedness or quasi-compactness assumption on f. Its proof points to the chart reduction of 0876 and to `flat.tex`, Tag 081P with the same label. The latter says “Some details omitted.” This delivery supplies those details rather than citing an unexpanded scheme version of the item as a new node.

The existing DAG theorem `lem-trf-flat-finite-type-dense-presentation` states Tag 081N for MODULES on an already locally finitely presented scheme morphism. It does not restate this item's conclusion about an arbitrary locally finite type SPACE morphism. Apply it on polynomial affine space, not on the morphism whose local finite presentation is still to be proved. This avoids a circular argument.

The imported blueprint lineage has `blueprint.from.node = null`; `python3 tools/blueprint_refs.py ancestor lem-sfb-space-flat-finite-presentation-dense-open` independently returns None. I preserved that lineage and its via list, and explained the current paragraph in split_report.blueprint. The current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), is the inherited compactification/direct-image context. This item is a supporting geometric finiteness lemma in that prerequisite chain, not the key statement of the unit; no chapter or unit record was modified and no unit route was changed.

## Not duplicates

No new nodes are proposed. Searched the whole DAG by 0877, 081P, 081N, schematic-density/finite-presentation wording, quotient kernels, affine flatness and associated-sheaf localization. Blueprint searches by `finite presentation dense open`, `schematically dense`, `finite presentation`, `081N`, `081P` and `0877` found no statement of this item. Reused the existing 081N theorem, 00R2 theorem, 0519(5) theorem, affine module criteria, and flatness criteria. In particular no scheme-only restatement of 0877, polynomial-quotient lemma, or elementary density lemma was created.

## Mathlib searches

The original item's search records are preserved. Read every result of six actual Q100 requests, retained in searches.jsonl and appended with their exact tool/query and results to mathlib_searches: LeanFinder on the geometric assertion, Loogle on Flat/LocallyOfFinitePresentation, grep for density/finite-presentation combinations in AlgebraicGeometry, LeanSearch on the assertion, LeanFinder on polynomial quotient kernels, and LeanFinder on a second algebraic phrasing of the geometric assertion. All services answered. The results give scheme definitions, flat-lfp consequences, or polynomial-quotient presentation facts, not extension of local finite presentation from a schematically dense open of an algebraic space. The algebra hits are already represented by the existing 00R2 and module-kernel nodes. No unrun query is recorded as Q100 work.

## Review by Q100

I read the chapter and unit records and SETUP's three levels, then read locally Stacks Tags 0877 and 0876 in spaces-more-morphisms.tex, 081P and the complete 081N argument in flat.tex, 00R2 (lemma-finite-presentation-independent) and 0519(5) (lemma-extension) in algebra.tex, 01PC (lemma-finite-presentation-module) in properties.tex, and 01TQ / 01U4 in morphisms.tex. There are no new nodes needing separate source review. I opened every cited node and checked its statement, not its proof, against the use described below; citations.json quotes those actual statements.

Step 1 uses the space morphism chart definitions, the definition of the small etale site and its regular-functions structure sheaf, the existing fibre-product/etale-cover theorem, and etale composition including open immersions. The restriction charts over V are genuinely etale. Schematic density is obtained by evaluating the GIVEN injective map of sheaves on scheme charts, not by assuming arbitrary base change preserves schematic density. Quasi-compactness of the inverse image on every affine etale chart includes every affine open of T. A finite affine subcover of a quasi-compact open then proves retrocompactness. This is the elementary chart unpacking in that step; it does not infer flatness or finite presentation from an atlas theorem left uncited.

Step 2 takes the affine cover with finite-type coordinate algebras directly from def-weil-finite-type-morphism and the polynomial surjection from def-weil-pbc-finite-type-algebra. The polynomial map has a finite presentation with zero relations. pqf-def-coherent, pqf-lem-associated-sections-localize and the full affine finite-type/presentation criterion give the associated quasi-coherent cyclic module and its sections. Generation by 1 proves finite type. There is no finiteness assumption on its kernel yet.

Step 3 uses lem-weil-pbc-flat-morphism-affine-criterion exactly for the coordinate algebra of a flat chart morphism. It then uses lem-pc-affine-chart-relative-flat-criterion with affine base T0, source H=Spec P, affine open H itself, and quasi-coherent F. Its statement gives actual relative-flat stalks from A-flatness of Gamma(H,F)=B. def-pc-scheme-module-flat-over identifies this with the hypothesis required by 081N. In particular this handles points outside the support, and does not require a flat closed immersion or a finitely presented coordinate algebra.

Step 4 uses lem-weil-pbc-lfp-affine-opens-finite-presentation on Spec B_a and Spec A_a inside the restricted morphism over W. These are affine opens of the correct source and target. The existing lem-weil-pbc-finite-presentation-surjection-kernel-fg applies to the FIXED localized polynomial surjection, so it really gives the kernel generators needed. The finite module presentation is written explicitly using those generators and def-sc-finitely-presented-module; it is not an unstated algebra-versus-module equivalence. The associated-sections formula and affine sheaf criterion identify that finite presentation with F on p^{-1}D(a). Such principal opens cover W0, so the definition of local finite presentation of module sheaves completes this verification.

Step 5 applies lem-trf-flat-finite-type-dense-presentation on H -> T0, whose local finite presentation was already proved. The preceding steps check ALL its hypotheses: F quasi-coherent finite type, relatively flat, W0 retrocompact and schematically dense, and F finitely presented above W0. Its conclusion is finite presentation of F; the affine sheaf criterion gives the precise global P-module finite presentation of B needed next. No part of the proof of the cited node is being borrowed as though it were its statement.

Step 6 uses lem-trf-finite-presentation-surjective-module-kernel with the cyclic source P and the now finitely presented target B. It gives finite generation of the kernel as a P-module, which is precisely finite generation as an ideal because the submodule lies in P. The resulting polynomial quotient is the definition of a finite algebra presentation. def-sbc-locally-finite-presentation and the chart definition then give the conclusion on the affine cover and for all compatible charts. No additional descent theorem or global separatedness is assumed.

I checked delivery-errors B1--B10: no statement-only children carry proofs because there are no children; the original self-contained statement is preserved; TeX uses single mathematical backslashes after JSON decoding; all source places have tags and labels; all searches were actually run; the project attachment check was negative. I checked C1--C8 and D1--D5 by the step-by-step statement audit above: every non-elementary input has a node; no proof-internal object of a cited theorem is used; the new argument is not a relabelling and has no self-reference. All external generic tools are declared in split_report.tool_uses with explanations. I checked E1--E7 against the actual affine bases and source/target of each map, rather than treating “restriction” as a substitute for a missing finite-presentation theorem.

Small cases: X empty is covered vacuously; Y empty forces X empty. If V=Y, the same proof applies with no boundary and recovers the given conclusion. If V is empty, schematic density forces O_Y=0 on every affine chart, hence Y and X empty, so it is not a counterexample. Noetherianity, reducedness and integrality of Y are never used; the sheaf-level density hypothesis accommodates nilpotents. The polynomial presentation also allows n=0 and the zero algebra B, where the displayed module and kernel arguments still hold. The proof works chartwise even when f is non-quasi-compact or non-separated. Each step is shorter than 2000 characters; none hides the entire assertion in a new lemma. No SGA source is used.

## Unfinished work

None in the stage-1 mathematical split. The required server dry run and delivery are the final operational checks.
