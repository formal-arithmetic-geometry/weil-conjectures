## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-characteristic-zero-log-resolution-independence.json: item, split into eleven source-following steps; statement unchanged.
- lem-per-qe-ordinary-regular-resolution: statement-only ordinary resolution theorem for all reduced Noetherian quasi-excellent rational schemes and regular morphisms; no Mathlib match.
- lem-per-normalized-tower-regular-pullback: statement-only normalization and regular-pullback calculus for centered towers; no Mathlib match.
- lem-per-log-monoidal-associated-points: statement-only ILO VIII 3.4.13, including its associated-center consequence; no Mathlib match.
- lem-per-normalized-tower-support-recovery: statement-only restriction/recovery and flat detection of ordered centered normalized towers; no Mathlib match.
- lem-per-rational-toric-completion-regular-map: statement-only regular maps from rational toric polynomial models to complete equicharacteristic log charts; no Mathlib match.

All five new node JSON files have the same chapter directory as the item. The sandbox also contains citations.json with a verbatim statement quotation for every cited node of every item step. No Lean file was written or compiled.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, log resolution, characteristic-zero resolution and resolution independence found no declaration stating this item. A sorry declaration would not have been an attachment.

## WANTED

None. All principal inputs are in the archived Illusie--Laszlo--Orgogozo volume, arXiv:1207.3648. The proof reads its Exposes VI and VIII, rather than citing an unavailable Temkin paper directly. No prohibited SGA source is used.

## Problems found and decisions

There was no earlier sandbox split, report or search log to reuse. I copied the live unsplit item and preserved its statement, source, ancestry and existing searches. I read the chapter and unit records, the latest blueprint ancestor proof, and the item's creation context in lem-per-complete-local-rigidification-comparison. The subargument remains the ILO VIII input supporting the ancestral geometric modification branch; it changes no chapter or unit route.

The live item bundles several theorems, and an apparent proof by applying 3.4.15 would merely repeat the statement. The delivery instead constructs the induced rule and writes the comparison argument: associated-point recovery reduces to the rational localization; complete toric models compare the two chart presentations; a single disjoint union of completions synchronizes their towers.

“Normalized desingularization” uses the source's definition VIII 2.3.2: centers have nonempty nowhere dense zero schemes. This is needed for the no-unit-center clause; a bare assignment of arbitrary normalized blowup towers would not suffice. “Ordinary blowups followed by normalization” is interpreted stage by stage as in VIII 2.2.6, not a single final normalization. These explain the existing statement, rather than change its mathematical hypotheses. A unit-center normalization that is nonidentity is never silently contracted in the general normalization input.

The rational localization X_Q need not be open: Spec(Z) -> Spec(Q) reversed supplies the familiar generic-point example. Step 7 therefore uses a quasi-compact flat monomorphism and schematic closure, exactly VIII 2.2.12, rather than an unjustified open-cover argument. No completion map of a non-qe original scheme is asserted regular. Only the maps from complete charts to rational toric polynomial models are regular. The coefficient fields for the two presentations need not coincide as embedded fields; the fixed algorithm is evaluated on the same underlying complete scheme.

## Not duplicates

lem-per-qe-ordinary-regular-resolution vs lem-trf-smooth-functorial-ordinary-resolution: the existing theorem covers finite-type rational schemes and smooth maps; this input covers all Noetherian qe rational schemes and all regular maps, including maps to complete local models.

lem-per-normalized-tower-regular-pullback vs lem-trf-normalized-resolution-on-normal-inputs: the existing statement assumes normal finite-type rational inputs and smooth comparison; this input includes the first normalization of a nonnormal qe input and regular, possibly non-finite-type, pullback.

lem-per-normalized-tower-regular-pullback vs lem-trf-smooth-normalization-quotient-comparison: that statement concerns smooth finite-type rational morphisms and their normalization cokernels; the new statement requires general regular base change and the normalization of centered blowup towers.

lem-per-log-monoidal-associated-points vs lem-per-characteristic-zero-log-resolution-independence: associated support is an independent lemma for an arbitrary monoidal tower, including mixed characteristic, with no resolution algorithm or two-log-structure comparison.

lem-per-normalized-tower-support-recovery vs lem-weil-pbc-local-completion-faithfully-flat: faithful flatness of one local completion alone does not state schematic recovery of centered towers from a flat monomorphism containing their associated-center images, nor the global equality test for their original indices.

lem-per-rational-toric-completion-regular-map vs lem-trf-log-regular-completed-chart: the existing theorem provides compatible completed ring presentations; it does not state regularity of the morphism from the rational toric polynomial model, or the qe domain needed to evaluate the algorithm.

I searched the full DAG statements, source locations, and relevant notions, and ran tools/blueprint_refs.py search for desingularization, monoidal/log geometry, associated points, toric models, normalization and completion. In particular I found and reused lem-trf-strict-fan-chart-local-comparison and lem-per-gabber-log-blowup-regularization instead of creating chart-comparison or strict-log-blowup nodes. The extra searches for those discarded candidate nodes remain in the real search log; no node is fabricated from them. All new nodes have precise blueprint.from.place and an empty same_as after these searches. No source carries a Stacks tag, because these combined assertions are ILO lemmas rather than a single Stacks result.

## Review by Q129

I read ILO VIII 2.1.18--2.1.20, 2.2.1--2.2.12, 2.3.1--2.3.12, 3.2.19--3.2.21, the proof of 3.3.15, 3.4.1--3.4.16, and VI 1.6(i). The item agrees with 2.3.10 plus the construction leading to 3.4.15 and its full comparison conclusion. New ordinary-resolution node A is 2.3.10 with the explicit definition of functoriality from 2.3.4--2.3.5; new normalization node B is 2.2.4(ii), 2.2.6, 2.2.9 and 2.3.3(i); new associated-point node C is 3.4.11 and 3.4.13, including the saturated case; new recovery node R is 2.1.18--2.1.20 and 2.2.11--2.2.12 with the completed local tests used on p.114; new regular-model node E makes explicit the rational model used in the third proof paragraph of 3.4.15 and the complete charts of VI 1.6(i). These are statement-only obligations, not relocated proof sketches.

For Step 1 I checked that A supplies the ordinary qe algorithm and that B supplies normalization at each stage and regular pullback, including the initial nonnormal case. For Step 2 I opened the statements of smooth-flatness, smooth-ring base change, smooth geometrically regular fibres, toric finite-type realizations, and torus-equivariance. The last one applies to the restriction of any chosen F on all reduced finite-type rational schemes, not merely toric maps; its projection/action comparisons retain actual ideals. Smooth maps are regular because of the first three inputs. The toric family therefore lies in the required qe domain.

For Step 3 I checked that monoscheme toric descent gives unique centered lifts and terminal smoothness, that tower-comparison coherence assumes exactly these unique lifts, and that the sharpening bijection is restricted to objects whose ordinary and sharp stalk groups are torsion free. Every fine torsion-free fan has the affine sharp lifts used by that bijection. The ideal correspondences preserve the unit condition. Step 4 uses the actual statement of strict-fan-chart-local-comparison, namely an isomorphism of localized chart fans with equality of chart maps. The existing chart-pullback and cover-rigidity statements then identify the ordered towers, while the finite-disjoint-union construction keeps their indexing. The descent theorem's chart-independence, strict-etale comparison, and composition assumptions are all supplied before invoking it.

For Step 5 I checked that gabber-log-blowup-regularization is stated for a fixed chosen smooth-functorial fan rule, allows disconnected separated Noetherian inputs without excellence, and gives the normalized stages and strict scheme-pullback comparison, not just existence of a regular modification. Its dependency closure does not contain the current item. Properness of the generated ring ideal is the explicit local-unit calculation from the log-structure definition. For Step 6 the cover-synchronization statement excludes stage deletion after a surjective strict etale cover; the recovery statement tests equality of ring ideals as needed even though the two log structures differ.

For Step 7 C says exactly that the associated points of the center quotients map into the canonical fan; it also records that nonempty centers have associated points. Both fans lie in the rational localization by the stated characteristic-zero hypothesis. R applies to this flat monomorphism and to all the Noetherian stages from Step 5. It recovers centers by schematic closure, so the argument proves equality on the whole scheme, including possible mixed-characteristic specializations. This step does not replace X_Q with an open subset.

For Step 8 the completed-chart node gives the monomial-compatible presentation after an allowed chart change. E supplies both regularity of the rational model map and the qe property of its complete target. Neither is taken from a definition of regularity. For Step 9 the toric descent and sharpening statements identify F on the rational monoid model with its induced log rule; the polynomial projection is smooth and surjective and loses no stage. The strict-pullback clause is from gabber-log-blowup-regularization, and the comparison is with F of the same complete underlying scheme. It is only contracted equality at this stage.

For Step 10 I checked the missing synchronization explicitly. C makes the union of the two fans finite and forces every center to have a witness over that set. R's faithfully flat completed strict local maps preserve these witness fibres. Adding the arbitrary test point and evaluating F on this one finite disjoint union makes both full towers equal to F(H); componentwise contractions are never substituted for that equality. Step 11 restricts the full equality without contracting and invokes the completed local equality test in R, then the earlier rational recovery and strict-etale descent. Thus every cited statement gives the clause actually used. citations.json copies the full statement of each cited node, so the relevant hypotheses and conclusion remain visible to the independent reviewer.

I tested the new statements and assembly on the empty scheme, length-zero towers, smooth/free monoids, P={0}, n=0, a singular saturated toric monoid, trivial log structure versus a normal-crossings divisorial structure on a regular scheme, unit-center identity stages, the first normalization of a nonnormal reduced input, and finite disjoint unions whose component resolutions have different lengths. The ordinary and normalized rules are distinguished at the first nonnormal stage; R requires actual uncontracted pullbacks; E requires characteristic zero and does not require k/Q finitely generated. The final argument uses regularity only for model maps, allowing a non-qe original X. These checks found the rational-localization issue and the need to state faithful local detection and nonemptiness of associated-point sets explicitly; I corrected those in the new inputs and the proof.

All eleven non-elementary steps are shorter than 2000 characters. Their non-elementary inputs are node citations; the local-unit calculation and restriction of an already synchronized full tower are written out. Mathlib searches for each new node used the required logged command with LeanFinder twice, LeanSearch, Loogle and grep; all services responded. I read the returned names and types. Normalization declarations, ordinary associated-prime facts, categorical fans, and scalar IsRegular predicates do not state these inputs. No Mathlib leaf is claimed. Blueprint ancestor and duplicate searches were done before writing the new nodes. The report does not claim an independent second reader: this is the direct-delivery worker's signed review.

## Unfinished work

No item proof step is left unwritten. The five new statement-only inputs await their own future stage-1 splits, as required by a one-level delivery. Dry-run and push results are recorded by the delivery tool.

## Dry-run repair

The first full dry run rejected a grouped definition citation in the new associated-point statement. I changed all grouped node references in new statements into individual bracketed references and refreshed the verbatim quotations. The mathematical statements and proof route are unchanged.

Final C1 refinement: Step 2 now explicitly cites lem-exc-fields-excellent and lem-exc-finite-type-localization-excellent to verify the qe domain for every reduced finite-type rational input. I opened both statements: the first gives excellence of Q, and the second gives excellence of its finite-type affine algebras. New statements also spell out the global Noetherian convention, fpqc cover, and schematic-closure ideal; these are definitions, not additional theorem obligations. The earlier dry run passed at 8c9c56d40f1; the refined delivery is dry-run again before pushing.
