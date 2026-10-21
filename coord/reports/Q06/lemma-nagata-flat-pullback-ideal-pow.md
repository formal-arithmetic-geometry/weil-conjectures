# Stage-1 report: lemma-nagata-flat-pullback-ideal-pow

## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-flat-pullback-ideal-pow.json`: statement, split; no sheaf-level Mathlib match. Replaced the imported single uncited paragraph with five proof steps using existing DAG nodes. Filled statement dependencies and blueprint same_as; retained the statement, blueprint_update, import flags and other import metadata.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The existing Mathlib leaf `lemma-nagata-localization-ideal-pow` supplies the general ring-map identity, not merely a localization special case. No unit record was changed: this item is not the unit's key statement.

## Attachments

No exact attachment for the item. `Ideal.range_powLiftBaseChange` (WeilConjectures/Blowup/FlatBaseChange.lean:49) and `Ideal.injective_powLiftBaseChange_of_flat` (line 75) are sorry-free in their displayed proofs and tagged with this blueprint id, but state the affine ring calculation, not the complete sheaf image equality. `AlgebraicGeometry.Scheme.IdealSheafData.comap_pow` (WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean:386) proves the extended-ideal equality, but its statement does not give the comparison with the image of module pullback. None meets the exact-attachment rule for the item.

`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_appLE` belongs to `lem-pc-ideal-sheaf-comap-affine-extension`, already recorded there. The current source is WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf/Affine.lean:95-109, rather than the stale line 92 in that node's attachment record. I read this proof, which has no sorry; this delivery does not change that node.

## WANTED

None. All sources needed here are available locally.

## Findings and corrections

The imported statement is correct. There is no STATEMENT-DISPUTED correction and no weakening. Flatness is stronger than necessary for this image equality; it remains in the statement. The imported proof used flatness to prove injectivity, which is not asserted by the item. The split instead uses the existing module-image comparison to justify the image and then performs the same affine ideal calculation. This stays within the Rees/affine-chart unit route.

The current main-20261015 blueprint file states the item without a proof; its blueprint_update preserves the imported affine argument. I therefore mark the expanded proof as agent-written, not as a verbatim human-written Stacks proof. Its geometric tools are sourced at Stacks 01JU (lemma-fibre-product-immersion), 01IN (lemma-closed-subspace-scheme) and 01IT (lemma-basis-affine-opens), whose local TeX and tag mappings I read. This proof uses only the affine ideal calculation within the unit and does not modify the unit or its route.

The original paragraph did not cite the module pullback/image comparison, the passage to affine charts or the ring identity. All are now explicit node citations. In particular, I do not identify the pullback module itself with an ideal without first taking its image, and I do not assume that inverse images or intersections of affine opens are affine.

The item’s Mathlib searches were made only with the required msearch.py command and are retained in searches.jsonl and mathlib_searches. LeanFinder and LeanSearch both found Ideal.map_pow, an affine ring result. Two initial Loogle patterns were rejected for unknown identifiers; the record says so, and the fully qualified comap query succeeded. It returned comap/comapIso and their functoriality, without the module-image/power statement. The grep searches found the affine ideal_pow formula at Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:424 and the comap definition at Functorial.lean:39, not the full item. I read these and Ideal.map_pow at RingTheory/Ideal/Maps.lean:669-670. The item requires a geometric comparison and local-to-global argument, so it is not a one-line specialization of Ideal.map_pow.

## Not duplicates

No new node was created. Whole-DAG keyword/name searches and whole-blueprint searches for ideal powers, extended ideals and related statements found the existing ring-power, ideal-power definition, extended-ideal definition, affine-extension and base-change-image nodes. Those are reused; no ring-power leaf, affine base-change lemma, sheaf-local-equality lemma or restatement of this item was introduced.

## Review by Q06

I read the item's imported proof, its current main-20261015 blueprint statement and blueprint_update, and its chapter/unit records. The intended affine ideal-power calculation is preserved. I checked the relevant Stacks source: 01JU explicitly identifies the base-changed ideal with the image of module pullback; 01IN supplies quasi-coherent closed-immersion ideals and affine descriptions; 01IT supplies affine neighborhoods inside arbitrary opens. I also read the actual project affine-extension declaration and Mathlib's ideal power/extension declarations. There are no new nodes needing a source review.

Step 1 uses the statement of def-sbc-ideal-sheaf-powers: products and powers are quasi-coherent and the zeroth power is the structure sheaf. The statement of lem-weil-pbc-quasi-coherent-ideal-closed-subscheme then constructs a closed immersion with exactly each ideal power as kernel. Its hypothesis is met for every m, including zero. No finite generation or Noetherian hypothesis is introduced.

Step 2 uses the full image clause of lem-pc-closed-subscheme-base-change-ideal-image, applied to those closed immersions. Its only geometric hypothesis is a closed immersion, already established; g can be any scheme morphism. The kernel formula in def-nagata-extended-ideal identifies that image with the extended ideal. The statement of def-sbc-closed-immersion-ideal-sheaf explicitly says the kernel is quasi-coherent, so using powers of J in the next steps is justified. Swapping the two fibre-product factors preserves the projection to Y by the universal property; this is only a change of notation, not an extra base-change theorem.

Step 3 uses lem-weil-pbc-affine-opens-basis twice, first at g(y), then in the open preimage on Y. It does not require that the whole preimage be affine. The statement of lem-pc-ideal-sheaf-comap-affine-extension has precisely the hypotheses now present: a closed immersion, any morphism g, and affine U,V with V contained in g^{-1}(U). It gives the ideal of sections of the base-changed closed subscheme, not just its support or a definition of pullback. The affine power formula from def-sbc-ideal-sheaf-powers identifies I^m(U) with I(U)^m. Those statements say every fact taken from them.

Step 4 uses the actual general ring-map statement of lemma-nagata-localization-ideal-pow: (I^n)B=(IB)^n for arbitrary commutative rings A,B and a unital map. Thus it applies to the sections map even though this need not be a localization. The affine power formula for the already quasi-coherent J finishes the equality of ideals of sections. I checked n=0 separately: the image of 1 is 1. With I=0 and n>0 both sides are zero; with I=A both sides are B. The zero ring and empty schemes cause no exception. As a non-flat diagnostic, take Z→Z/2 and I=(2): the tensor module can be nonzero while its map to Z/2 has zero image; both ideals in the claimed equality are nevertheless zero. This confirms why the statement is about the image and why no injectivity inference is used.

Step 5 again uses exactly the neighborhood form of the affine-basis node, now refining any open T. It writes out local membership and sheaf gluing in both directions. Agreement of the local sections is checked inside the ambient structure sheaf using the injective inclusions; uniqueness there identifies the glued section. It is an elementary sheaf-axiom argument, rather than a hidden claim that equality on one set of affine sections automatically gives a sheaf equality. Every non-elementary step has all its tool statements cited; every cited statement was opened and copied in citations.json. No step exceeds 2000 characters and no step hides a separate comparison lemma.

The two off-unit statements are generic geometric tools, declared in split_report.tool_uses: the closed-subscheme module-image theorem and its affine ideal-extension formula. They do not replace the unit's affine/Rees route. All other proof tools are existing definitions or Mathlib leaves. The new proof does not depend on any node that depends on this item.

I checked delivery-errors B–E against the files: no new statement-only node, notation, duplicate, or source-tag issue arises; no unsupported flatness/exactness assertion remains; no definition is cited in place of the image theorem; the actual ring computation and sheaf gluing stay in the item rather than being moved into a new restatement node. citations.json contains a verbatim substring of each cited node's statement for every use. The final dry run and delivery results follow below.

## Unfinished work

None in the stage-1 split. No Lean was written, no compiler/Lake/build command was run, and no shared-repository or launcher file was written.

## Validation log

The first captured dry run stopped at the citation gate because the displayed ring-power formula alone was shorter than its minimum quotation length. Replaced that quotation with the full existing node statement, including its arbitrary ring-map hypotheses. The mathematical split was unchanged.


## Repair of the 2026-10-21 return

The returned branch head is `f9d4ae35837`, as recorded in `coord/returns/Q06.md`. Its retained delivery is the sandbox version read at the start of this repair. The return reports an approved mathematical reading followed by refusal to land a side completion that had not reached the live DAG. I compared that retained version with the current read clone: the live item is still `imported`, with its original uncited paragraph and only the extended-ideal statement dependency; the retained delivery supplies the five-step split. Their statements, chapter/unit, source and blueprint_update agree. No completion claim in the side DAG is used as evidence that the live item is finished.

The required initial dry run rebuilt the retained split on current `origin/sheaf-dag` and exited successfully at `2b3b63c503d` with `OK (not pushed)`. This confirms packaging against the current delivery base; promotion and final landing remain the maintainer's operation. I have not edited the live DAG or its queue, any launcher file, or any maintainer-owned field.

I reopened every live statement dependency: def-pc-scheme supplies schemes and affine opens; pqf-def-coherent supplies quasi-coherence; def-weil-flat-morphism defines flatness at stalks; def-pc-module-pullback specifies the Zariski module pullback and its structure map; def-sbc-ideal-sheaf-powers supplies the quasi-coherent product and affine power formula; def-nagata-extended-ideal defines extension by the kernel of the base-changed closed subscheme. The latter kernel definition is why the proof retains its explicit comparison with the module sheaf image.

For the proof dependencies I reread the full current statements, not just their attachment/status records. In step 1, the power definition gives quasi-coherent products and the closed-subscheme existence statement gives a scheme with precisely the prescribed kernel, without a finite-type assumption. In step 2, lem-pc-closed-subscheme-base-change-ideal-image gives the actual composite module map and its sheaf image, while the extended-ideal definition gives its kernel description and the closed-immersion-ideal definition gives quasi-coherence. In step 3, the affine-basis statement permits neighborhoods inside any prescribed open, and lem-pc-ideal-sheaf-comap-affine-extension gives ideal extension on every adapted affine pair. In step 4, lemma-nagata-localization-ideal-pow still states the arbitrary unital ring-map identity, so no localization hypothesis is being silently assumed. In step 5 the same affine-basis statement refines every open T, and the written sheaf-axiom argument proves both inclusions. All existing citation quotations remain valid in the current statements. The generic tools still have status split and are explicitly declared in split_report.tool_uses; neither a completion status nor an unproved Lean attachment is used as a premise.

I adjusted the split rather than merely repushing it. Step 1 now writes out the induction establishing quasi-coherence of all powers and chooses the canonical closed subschemes V(I^m) used by the live extended-ideal definition. Its quotation now includes the quasi-coherent product clause. Step 3 now explicitly distinguishes sections of the sheaf image from the image of a map on sections, which need not agree in general. These changes make the hypotheses and the image comparison visible under the current DAG definitions; the item statement and proof route are unchanged. No cited statement requires a replacement node, and no new node or search is necessary. I retained and reread all seven recorded search results in searches.jsonl, including the two rejected Loogle patterns and their successful retry.

I reread the current main-20261015 item, the chapter/unit records, Stacks 01IN (lemma-closed-subspace-scheme), 01JU (lemma-fibre-product-immersion) and 01IT (lemma-basis-affine-opens), the project affine-extension declaration at Affine.lean:95-109, and the project tagged ring declarations at FlatBaseChange.lean:49 and :75. The tagged declarations still cover only the ring calculation, while comap_pow at Functorial.lean:386 states ideal-data extension without the module-image comparison; none supplies an exact attachment. The retained Mathlib search hits still say exactly the ring power identity, affine power definition and kernel definition reported above. The edge cases n=0, zero and unit ideals, the zero ring and empty schemes remain valid. Every non-elementary step is below 2000 characters and names the current statements that supply its facts. This repair introduces no duplicate, hidden lemma, added hypothesis or unsupported exactness claim under delivery-errors B–E.
