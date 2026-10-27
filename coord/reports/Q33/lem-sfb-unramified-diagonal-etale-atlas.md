# Worker report — Q33

## Files written

`dag/nodes/sec-six-functors-basics/lem-sfb-unramified-diagonal-etale-atlas.json`: item, split into eleven steps; statement unchanged. `citations.json` contains a verbatim statement excerpt for every citation of every step.

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-type-point-etale-self-relation.json`: statement only, unsplit, no Mathlib match.

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-etale-monomorphism-open.json`: statement only, unsplit, no Mathlib match.

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-unramified-open-diagonal.json`: statement only, unsplit, no Mathlib match.

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-unramified-permanence.json`: statement only, unsplit, no Mathlib match.

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-chartwise-smooth-etale-calculus.json`: statement only, unsplit, no Mathlib match.

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-fibre-regular-slice-flat.json`: statement only, unsplit, no Mathlib match.

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-fibre-unramified-etale.json`: statement only, unsplit, no Mathlib match.

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-flat-lfp-finite-type-surjectivity.json`: statement only, unsplit, no Mathlib match.

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-representable-unramified-descent.json`: statement only, unsplit, no Mathlib match.

## Attachments

None. Exact-tag and conceptual searches in lean/WeilConjectures found scheme results, not this item or any of the new algebraic-space/stack lemmas. No sorry-free project declaration covers the item. The inherited Mathlib searches on the item were read and preserved.

## Wanted literature

None. The needed Stacks sources are present locally.

## Faults and changes

The item had a correct statement but no proof. The proof now constructs the étale charts and proves the converse by descent. No statement dispute or change of the unit route was found. The relative diagonal over S is retained; 050N translates the absolute DM convention for the residual-gerbe input. The base need not be Noetherian, k need not be perfect, and the atlas need not be quasi-compact.

The first dry run found additional overlapping nodes in the live server DAG. I read them and narrowed the new open-diagonal statement to part (2) of 05W1: the existing lem-sfb-unramified-space-open-diagonal states only part (1). I removed the proposed scheme-parameter child entirely. Its construction is now explicit in steps 5, 6 and 8, citing the existing separable-points, smooth-regularity, local unramified-criterion, Nakayama and regular-generator nodes. The report records the other overlaps below.

The canonical ancestor command returns None for this item. Its blueprint.from.node was already null, and children preserve that canonical ancestor and prepend this item to its inherited via chain. Their places describe the precise support for the inherited alteration/moduli route. Both the unit record and the current main-20261015 unit text were read. This is not the unit key node, so no realization fields were changed. The proof has seven explicit generic tool uses recorded in split_report; no maintainer-owned tool_uses was set.

## What could not be finished

No mathematical part of this one-level split remains unhandled. The nine new inputs intentionally remain statement-only unsplit nodes. This is not a claim that their Lean proofs have been completed.

## Search audit

Before creation I searched the entire DAG by the relevant tags and concepts and the entire imported blueprint with blueprint_refs.py search (unramified diagonal, Deligne, étale atlas, residual gerbe, slice, regular sequence, étale monomorphism, finite-type points, unramified descent, and source tags). I read the statements of all proof citations. Existing generic algebraic-space étale calculus, scheme coproduct, dense separable points and the four local algebra/scheme lemmas are reused.

Each new node has two LeanFinder phrasings, LeanSearch, Loogle and a Mathlib source grep, run with msearch.py, read and recorded exactly as returned. All services answered. The scheme-only FormallyUnramified diagonal instances, flat-monomorphism open-immersion theorem, smooth charts, regular-sequence ascent, and scheme descent are not the algebraic-space/stack assertions stated by these nodes. The item’s earlier actual searches are retained. No unsuccessful service was labelled no match. The deleted parameter node’s searches remain in the append-only log as provenance.

## Not duplicates

- lem-sfb-space-unramified-permanence vs lem-sfb-dm-isom-space-unramified: the existing node asserts unramifiedness of a DM stack’s Isom space; this child gives base change, composition and right cancellation for arbitrary algebraic-space maps.

- lem-sfb-finite-type-point-etale-self-relation vs lem-sfb-algebraic-stack-dm-point-stabilizer: the existing node tests membership in a DM locus using a given stabilizer; it does not choose a locally finite type field representative with étale self-relation.

- lem-sfb-finite-type-point-etale-self-relation vs lem-sfb-unramified-diagonal-etale-atlas: the child gives a locally finite type field representative and its étale self-relation at one finite-type point; it supplies no étale neighbourhood or atlas. Those are constructed by the item’s slices.

- lem-sfb-finite-type-point-etale-self-relation vs lem-sfb-representable-finite-stack-properties: the existing node transfers DM/proper/quasi-finite properties along a representable finite stack map; the child concerns a point and its field self-relation, with no finite stack map assumed.

- lem-sfb-finite-type-point-etale-self-relation vs lem-sfb-algebraic-stack-open-dm-locus: the existing node constructs the maximal open with unramified diagonal; it does not construct the required field representative.

- lem-sfb-finite-type-point-etale-self-relation vs lem-sfb-dm-isom-space-unramified: the existing node concerns Isom spaces of two objects in a stack already known to have an étale atlas; the child constructs a field representative under the unramified-diagonal hypothesis, before an atlas is known.

- lem-sfb-finite-type-point-etale-self-relation vs lem-sfb-curve-stack-infinitesimal-dm-locus: the existing node describes the DM locus of the stack of proper curves; the child supplies field representatives in arbitrary algebraic stacks with unramified diagonal.

- lem-sfb-stack-chartwise-smooth-etale-calculus vs lem-trf-space-chartwise-etale-permanence: the existing node gives étale calculus for algebraic spaces; this child treats representable maps with stack targets, smoothness/flatness/local presentation and the disjoint-source construction.

- lem-sfb-stack-chartwise-smooth-etale-calculus vs lem-sfb-dm-isom-space-unramified: the existing node concerns a DM stack’s Isom space; this child states the general chartwise calculus for representable maps, without assuming any étale atlas of the stack.

- lem-sfb-space-unramified-open-diagonal vs lem-sfb-unramified-space-open-diagonal: the existing node assumes unramified and concludes open diagonal (05W1 part (1)); this child assumes local finite type and open diagonal and concludes unramified (part (2)), the direction needed in step 4.

- lem-sfb-space-unramified-open-diagonal vs lem-sfb-dm-geometric-inertia-trivial: the existing node realizes a DM stack with trivial geometric inertia as an algebraic space; it does not state the converse open-diagonal criterion for arbitrary locally finite type space morphisms.

## Review by Q33

I read the full proof of 06N3 (theorem-DM) in stacks-morphisms.tex and the relative-base comparison 050N. The item agrees with both, including arbitrary S and both directions. The proof follows its residual-gerbe, regular-slice and finite-type-point route. All non-elementary facts used in the proof are now named citations; the elementary fibre-product and definition steps are written out. No step exceeds 2000 characters.

For the nine child statements, I checked these source places and hypotheses:

- lem-sfb-finite-type-point-etale-self-relation: literature/stacks-project/stacks-morphisms.tex, Tags 06G3 (lemma-point-finite-type-monomorphism), 06MZ (lemma-separation-properties-residual-gerbe), 06N0 (lemma-DM-residual-gerbe); their combination is the first construction paragraph of Tag 06N3 (theorem-DM). Relative diagonal convention: Tag 050N (lemma-separated-implies-morphism-separated), (1).

- lem-sfb-space-etale-monomorphism-open: literature/stacks-project/spaces-morphisms.tex, Tag 05W5 (lemma-etale-universally-injective-open), monomorphism specialization.

- lem-sfb-space-unramified-open-diagonal: literature/stacks-project/spaces-morphisms.tex, Tag 05W1 (lemma-diagonal-unramified-morphism), part (2). The reverse implication is already represented by lem-sfb-unramified-space-open-diagonal when the target is a scheme.

- lem-sfb-space-unramified-permanence: literature/stacks-project/spaces-morphisms.tex, Tags 03ZI (lemma-composition-unramified), 03ZJ (lemma-base-change-unramified), 06G6 (lemma-permanence-unramified), 06CR (lemma-etale-unramified).

- lem-sfb-stack-chartwise-smooth-etale-calculus: literature/stacks-project/stacks-properties.tex, Section 04XB (section-properties-morphisms), including Tag 04XC (lemma-property-spaces-too); algebraic.tex Tags 045B (lemma-composition-representable-transformations-property), 045C (lemma-base-change-representable-transformations-property), 045G (lemma-representable-diagonal); spaces-morphisms.tex Tags 03ZD, 03ZE, 03ZF, 04AJ, 04TA, 04XX for smoothness, and spaces-properties.tex Tags 03FT, 03FU, 03FS for etaleness. Surjectivity: stacks-properties.tex Tags 04ZT, 04ZU. The disjoint-source clause is source locality and stack descent on the disjoint open cover.

- lem-sfb-stack-fibre-regular-slice-flat: literature/stacks-project/stacks-morphisms.tex, Tag 06MD (lemma-slice), scheme-source specialization; the etale-chart formulation of the regular-sequence hypothesis is the strict-local-ring formulation there, since these local maps are faithfully flat.

- lem-sfb-stack-fibre-unramified-etale: literature/stacks-project/stacks-morphisms.tex, Tag 06N2 (lemma-etale-at-point); its fibre hypothesis expressed on an etale scheme chart, using the etale-local definition of unramifiedness.

- lem-sfb-stack-flat-lfp-finite-type-surjectivity: literature/stacks-project/stacks-morphisms.tex, Tag 06G2 (lemma-enough-finite-type-points), combined with stacks-properties.tex Tags 04XL (lemma-topology-points), (2), and 04XI (lemma-characterize-surjective); the open-image criterion used in the final paragraph of theorem-DM.

- lem-sfb-stack-representable-unramified-descent: literature/stacks-project/stacks-properties.tex, Tag 04XD (lemma-check-property-covering), for P = unramified, as listed in Section 04XB (section-properties-morphisms).

The field-representative input combines 06G3, 06MZ and 06N0, with 050N for the relative convention. The locally Noetherian and reduced hypotheses of 06N0 belong to the residual gerbe, not the arbitrary stack. The representative is locally finite type, not asserted étale over the stack; a closed point of positive-dimensional affine space confirms that distinction. The self-relation is étale because the field map to its gerbe is étale and the gerbe inclusion is a monomorphism.

For unramified permanence I checked 03ZI, 03ZJ, 06G6 and 06CR. Right cancellation has no hypothesis on the second map. For the diagonal input I use only 05W1 part (2) and retain local finite type. For the étale-monomorphism input, 05W5 applies because a sheaf monomorphism is universally injective. Identity maps and empty spaces pass these statements; the two-copy étale cover of a point does not satisfy the monomorphism hypothesis.

I read 06MD and 06N2. The regular-slice and fibre-étale children are formulated with a scheme chart of the field fibre. This is equivalent to the source formulations: regularity passes to the common strict local ring through the faithfully flat local map from the étale chart, and unramifiedness is étale local on the source. Both children explicitly retain flatness and local finite presentation. For an empty equation list, 06MD returns the original map; a unit fails the regular-sequence condition because its quotient is zero. The hypotheses do not imply that an arbitrary closed subscheme is flat.

I read 06G2, 04XL and 04XI for finite-type-point detection. A flat locally finitely presented map has open image; any nonempty closed complement contains a finite-type point. Neither Jacobson nor Noetherian hypotheses are needed, and the empty stack satisfies the result. I read 04XD and the unramified entry of 04XB for the descent child. The tested morphism is representable, the cover is surjective flat locally finitely presented, and no global quasi-compactness is inserted. The general chartwise calculus follows the extension-of-properties discussion of 04XB and the individual smooth/étale/base-change/locality tags listed above; the disjoint-union clause uses stack descent on the disjoint open cover, not existence of an étale atlas for an arbitrary stack.

Step 1 uses the triple description and the actual representable-diagonal definition from the moduli-groupoid node and the algebraic-space definition. The displayed base-change identity is its elementary argument. Step 2 takes exactly the base-change/product clauses of the calculus child, the cancellation clause of unramified permanence, and the descent child. The cover used to test the relative diagonal is W times_S W; its pullback is R = W times_X W.

Step 3 takes the chosen field representative and both étale projections from the first child, and base change from the calculus child. The field fibre is nonempty because the atlas is surjective. Step 4 takes the “any map between spaces étale over F is étale” sentence of the existing lem-trf-space-chartwise-etale-permanence; it applies to the diagonal section. Its monomorphism is checked in the step. The two new inputs then give open diagonal and unramifiedness. The existing forward-only diagonal theorem was not misused as its converse.

Step 5 uses the algebraic-space atlas definition to choose a nonempty affine chart, composition in the calculus and unramified-permanence nodes, and lem-pc-dense-separable-points to obtain the finite separable point over the possibly imperfect field k. Step 6 uses def-sbc-smooth-morphisms for affine-local smoothness and lem-weil-pbc-smooth-over-field-regular-local for the local ring B. The exact maximal-ideal equality comes from lem-trf-unramified-maximal-ideal-residue-criterion. The chosen images span modulo its square; Nakayama applies to the finitely generated maximal ideal of the Noetherian local ring B. The minimal generators are regular by lem-weil-pbc-regular-local-generators-regular-sequence. A finite collection of germs spreads to one common open neighbourhood by the definition of a stalk. This is the parameter argument written in the item, not a new wrapper lemma.

Step 7 uses smooth implies flat and locally presented, then the regular-slice statement, with the regularity checked at v on V_0. Every shrinking retains u and thus v. Step 8 identifies the local ring of the actual zero scheme T with B divided by its maximal ideal. T is locally finite type over k by the affine quotient description, and its residue field is finite separable. These are exactly the hypotheses of the same unramified local criterion used in step 6; it gives an unramified neighbourhood of v. For affine d-space and the identity map the functions are coordinate parameters; for a finite separable field the empty list is allowed.

Step 9 uses base change in the calculus statement and the fibre-étale child. Its chart is exactly T = Z times_U V_0; the equation pullback and retention of v were checked. Thus W_x still contains a point above x. Step 10 uses the actual scheme-coproduct statement and the disjoint-source clause of the calculus child, then finite-type-point detection. One fixed smooth U is used for all x; point classes are a quotient of the points of U (surjectivity means a field object lifts after a field extension), and each W_x is locally closed in U. Hence both the indexing set and the family of local constructions have a common bound in the same universe. The empty family gives the empty atlas of the empty stack. Step 11 uses the exact Deligne–Mumford definition and is elementary.

This checks B1–B10, C1–C8, D1–D5 and E1–E7 against the actual files: self-contained statement-only children, correct tags/labels and TeX, genuine logged searches, explicit notions, exact cited statements, no citation of a proof instead of its statement, no added geometric hypotheses, and no child asserting either clause of the item. citations.json has verbatim excerpts for every step/node pair. New inputs are smaller independent tools (field representative, local slice, local fibre test, property descent and space criteria), not a relabelled atlas-existence theorem. No Lean or compiler tool was used. I corrected the overlap handling and expanded the parameter argument after the first dry run; the maintainer supplies the independent review.

## Validation

The preliminary server-side review_split passed. The first deliver.py dry run stopped at the overlap-report gate before server preflight; the overlaps are now handled by the narrowed direction, reused nodes, and explicit pairs above. A final dry run is run next.
