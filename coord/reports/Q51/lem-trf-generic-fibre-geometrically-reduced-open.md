# Q51: lem-trf-generic-fibre-geometrically-reduced-open

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-fibre-geometrically-reduced-open.json`: item, statement unchanged; eight proof steps following Stacks 0578; status split. Mathlib has no exact or one-line match.
- `dag/nodes/sec-trace-formula/lem-trf-schematic-density-generic-fibre-open.json`: new statement-only lemma, Stacks 0573; unsplit, not a Mathlib leaf.
- `citations.json`: verbatim statement quotations for every step/node citation, including the new child.
- `report.md`: this report. `searches.jsonl` is the search command's existing append-only record; `write_split.py` is sandbox scratch for constructing the JSON.

There is one new node and zero new Mathlib leaves. No Lean file, compiler, Lake invocation, live repository file or launcher script was written or run. The sandbox initially contained only launcher brief markers, so there was no previous split or report to discard and no running delivery to repeat.

## Attachments

None for the item. Searches of the read-only project source by the exact blueprint id and by generic-fibre/geometric-reducedness concepts found no declaration giving this item. The nearby project theorem `AlgebraicGeometry.GeometricallyReduced.dense_smoothLocus` at `WeilConjectures/AlgebraicGeometry/Morphisms/SlicingFlat.lean:130` already belongs to `lem-pur-geometrically-reduced-dense-smooth-open`; I reuse that closed node. Smooth geometric reducedness and the two schematic-density tools already have closed audit records, and I reuse their nodes without changing them.

## WANTED

None. The item and new child's sources are present in the Stacks checkout.

## Problems found and repaired

The imported statement agrees with Stacks 0578, including allowing a nonreduced or non-Noetherian irreducible base and empty fibres; no statement dispute or change is needed. Its proof was absent. The source's last application of reducedness must be understood after every residue-field extension, not just on the ordinary fibre. Steps 7 and 8 make this inference explicit using flat pullback of schematic density. I also made the quasi-compactness assumptions on the existing dense-image tools explicit in step 3. Finite type over a field supplies topologically Noetherian fibres even though the original morphism need not be quasi-separated. Generic flatness is used only after reducing to an integral base. Only local finite presentation, which the cited generic-flatness node actually states, is used; no finite-presentation/quasi-separatedness clause is silently taken from it.

During source checking I corrected the density characterization tag to 01RE (`lemma-characterize-scheme-theoretically-dense`); 0573 is the child theorem and 0578 is the item. The item remains at its inherited chapter/unit and descendant route; I read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the current main-20261015 ancestor statement/proof. This is the existing 0579/0578 constructibility input on the semistable-alteration/flattening branch, not a replacement of that unit's proof. The item is not the unit's key statement, so no unit record is changed.

## Unfinished work

No unfinished part of this one-level split. The new 0573 node is intentionally statement-only and will be split as its own item. Its actual Stacks proof reduces to affine charts and spreads injectivity using generic freeness and a flat cokernel; that argument belongs to 0573, not to this report's item. Server dry run and push results are recorded below when available.

## Mathlib and duplicate searches

Read the actual results of all logged searches. The item was searched by LeanFinder twice in different formulations, Loogle, LeanSearch and source grep. The child was searched by LeanFinder twice, Loogle, LeanSearch and source grep. The records preserve exact query text and the search-command result summaries/digests. Returned global geometric-reducedness declarations assume the fibre property already; none spreads it from a generic point. Returned `spread_out_of_isGermInjective` declarations spread a morphism from stalk data, not schematic density in all nearby fibres. I read `Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean:35-137` and `Mathlib/AlgebraicGeometry/Morphisms/SchemeTheoreticallyDominant.lean:35-137`. The latter supplies the existing density/pullback tools, not 0573. Extra exploratory searches for elementary reducedness facts remain in the log but have produced no redundant node.

Whole-DAG searches used the tag/label and schematic-density phrases, and `tools/blueprint_refs.py search` was run for “scheme theoretically dense”, “scheme-theoretically dense”, “schematically dense”, “schematic density”, “density”, “0573”, “056D”, “056E”, “geometrically reduced”, “geometrically reduced generic fibre” and “generic flatness”. The ancestor command gives `lem-trf-local-term-locality`, which the item and new child record with their full inherited via chains. No blueprint node states 0573.

## Not duplicates

- `lem-trf-schematic-density-generic-fibre-open` vs `lemma-nagata-dense-flat-pullback`: the existing statement preserves the schematic image under a supplied flat base change; the child constructs an open of the base on which every fibre inclusion becomes schematically dense, without assuming those fibre maps flat.
- `lem-trf-schematic-density-generic-fibre-open` vs `lemma-nagata-reduced-dense-image-schematic`: the existing statement upgrades a supplied dense image into a reduced target to schematic density, with no family or open-shrinking conclusion; the child assumes generic schematic density and propagates it to nearby fibres, whose reducedness is not assumed.
- `lem-trf-schematic-density-generic-fibre-open` vs `lem-trf-generic-fibre-geometrically-reduced-open`: the child is a theorem about an arbitrary open in a family and injectivity of its structure-sheaf restriction. It says nothing about smoothness or reducedness of that open or its ambient fibre. The item's steps construct the appropriate smooth open, supply its generic density, and recover geometric reducedness after field extension. Thus the child is not the item or one of its conclusion clauses.

No existing node has Stacks 0573 as its source. Whole-file grep finds incidental numeric digests and historical log identifiers containing those digits; those statements do not concern schematic density in a generic fibre.

## Review by Q51

I read Stacks `more-morphisms.tex` Tag 0578, `lemma-geometrically-reduced-generic-fibre`, statement and whole proof (lines 7215–7255), and checked the imported statement clause by clause. I also read the whole statement and proof of 0573, `lemma-scheme-theoretically-dense-generic-fibre` (lines 6563–6641), for the new child. Its hypotheses are exactly finite type, irreducible base with generic point, and schematic density of the supplied generic open. Its conclusion is the nonempty open with density on all ordinary fibres. I read the 01RB definition and 01RE injectivity characterization in `morphisms.tex`; the child writes this characterization explicitly so it does not misuse the existing quasi-compact-only definition node for arbitrary opens. The child contains no proof sketch and all its objects are introduced.

For step 1 I opened `lem-weil-pbc-reduction-universal-homeomorphism`, `def-weil-pbc-scheme-reduction`, `def-pc-integral-scheme`, `def-pc-scheme-fibre`, and `lem-sfb-finite-type-composition-base-change`. They give respectively reducedness and the homeomorphism, the nilradical quotient, integral iff reduced and irreducible, the fibre product, and stability of finite type. I wrote the residue-field calculation and fibre-product reassociation, rather than assuming a general universal homeomorphism identifies fibres. An arbitrary universal homeomorphism would not give that identification; it is the nilradical quotient that does here.

For step 2 I opened `lem-sbc-generic-flat-finite-presentation`, `def-sbc-locally-finite-presentation`, the finite-type base-change theorem, and `lem-weil-pbc-fibre-product-affine-spectra`. The generic-flatness statement applies to the reduced integral base, and gives precisely flatness and local finite presentation. The displayed finite polynomial presentation after tensoring is an explicit elementary verification that the generic fibre has the local finite-presentation hypothesis for the smooth-locus theorem.

For step 3 I opened the finite-type definition/base-change statements, `lem-weil-pbc-finite-type-algebra-noetherian`, `lem-sc-affine-noetherian-underlying-space`, and `lem-sfb-noetherian-space-compact-subsets`. They give exactly the finite affine covering, Noetherian coordinate rings and topological spaces, and compactness of subsets. The finite-cover descending-chain argument is written out. This proves the quasi-compactness needed in steps 5 and 7 without assuming the smooth open of the original total space is quasi-compact. Open immersions are quasi-separated because their diagonal is an isomorphism.

For step 4 I opened `lem-pur-geometrically-reduced-dense-smooth-open`, `lem-trf-smooth-at-point-fibre-criterion`, `sbc-lem-smooth-geometrically-reduced`, `lem-trf-reduced-scheme-open-cover`, and `def-pc-geometrically-irreducible`. I also read Stacks 056V, 01V9 and the source declaration at SlicingFlat:130–134. The dense-locus node has an arbitrary field and local finite presentation; no perfect-field hypothesis is introduced. The pointwise criterion requires exactly the flatness and local finite presentation obtained in step 2. The argument covers the chosen union by smooth opens, so smooth-fibre reducedness and the open-cover node give geometric reducedness of each $U_y$ without needing to cite a smooth-gluing theorem.

For step 5 I opened `lemma-nagata-reduced-dense-image-schematic`, read both its actual statement and its current blueprint update, and used only the older, stronger-hypothesis statement: our inclusion is both quasi-compact and quasi-separated by step 3. Its target is reduced by the identity field extension. The existing image definition explicitly describes the kernel of the structure-sheaf map; the uses and quotation give exactly that part. Stacks 056D confirms this use.

For step 6 the child gives exactly the sheaf-injectivity conclusion used: finite type remains true after both base restrictions, irreducibility remains true on each nonempty open of the integral base, and step 5 supplies the generic hypothesis. There is no citation of the child's proof or of a definition for its theorem.

For step 7 I opened the affine fibre-product theorem, `lem-weil-pbc-field-extension-base-change-faithfully-flat`, `lem-weil-pbc-flat-ring-map-iff-flat-affine`, `lemma-nagata-dense-flat-pullback`, the image definition and the reduced-scheme definition. The ring statement explicitly provides faithful flatness of $D\to D\otimes L$; its weaker flatness conclusion meets the affine criterion. The dense pullback node requires quasi-compactness and quasi-separatedness of the inclusion and flatness of the target map; these hold by step 3 and the preceding ring calculation. I read Stacks 081I in full. Restriction to affine charts avoids any unstated general flat-base-change stability theorem. The fibre cover after extension is the actual pullback cover.

For step 8 I opened the section-wise reducedness definition and the reduced open-cover theorem. A nilpotent section maps to zero on the reduced open; injectivity forces it to vanish, which is a two-line argument. The definition of geometric reducedness quantifies over all field extensions, and step 7 used an arbitrary one. This is the needed 056E argument, not a new lemma and not a hidden claim that density alone survives arbitrary base change.

I checked small cases. If the generic fibre is empty, its smooth open and density are empty, and 0573 forces nearby fibres to be empty as well; the conclusion remains correct. A one-point nonreduced base such as $\operatorname{Spec}k[\epsilon]/\epsilon^2$ reduces without changing any residue-field fibre. Over imperfect fields the smooth-locus input assumes geometric reducedness, so a purely inseparable nonreduced geometric extension is not accidentally admitted. The child also allows $U=X$ and empty $X$; taking $V=Y$ is consistent. Ordinary density in a doubled/nonreduced point would not imply schematic density; the injectivity hypothesis explicitly excludes this. Every non-elementary step cites a theorem that says what it takes, all quotations are verbatim, and every step has fewer than 2000 characters.

Only `lem-sbc-generic-flat-finite-presentation` is a nonclosed off-unit theorem tool; it is declared in `split_report.tool_uses` as the generic-flatness black box required by the Stacks route. Definitions, Mathlib leaves and existing closed nodes supply the other generic tools. I did not write maintainer-owned `tool_uses` fields or alter their nodes.
